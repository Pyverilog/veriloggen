from __future__ import absolute_import
from __future__ import print_function

import math
import functools
from collections import OrderedDict

import veriloggen.core.vtypes as vtypes
import veriloggen.types.axi as axi
from veriloggen.fsm.fsm import FSM
from veriloggen.optimizer import try_optimize as optimize

from .ttypes import _MutexFunction
from .ram import RAM, MultibankRAM, to_multibank_ram
from .fifo import FIFO


class AXIStreamIn(axi.AxiStreamIn, _MutexFunction):
    """ AXI Stream Interface for Input """

    __intrinsics__ = {'read': 'read',
                      'dma_read': 'dma_read',
                      'dma_read_async': 'dma_read_async',
                      'dma_wait_read': 'dma_wait_read',
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 with_last=True, with_strb=False,
                 id_width=0, user_width=0, dest_width=0,
                 noio=False,
                 op_sel_width=8, req_fifo_addrwidth=3, fsm_as_module=False):

        axi.AxiStreamIn.__init__(self, m, name, clk, rst, datawidth,
                                 with_last, with_strb,
                                 id_width, user_width, dest_width,
                                 noio)

        self.addrwidth = addrwidth

        self.op_sel_width = op_sel_width
        self.req_fifo_addrwidth = req_fifo_addrwidth
        self.fsm_as_module = fsm_as_module

        self.mutex = None

        # Read
        self.read_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'read_req_fifo']),
                                  self.clk, self.rst,
                                  datawidth=self.op_sel_width + self.addrwidth * 3 + 1,
                                  addrwidth=self.req_fifo_addrwidth,
                                  sync=False)

        self.read_op_sel_fifo = self.m.Wire('_'.join(['', self.name,
                                                      'read_op_sel_fifo']),
                                            self.op_sel_width)
        self.read_local_addr_fifo = self.m.Wire('_'.join(['', self.name,
                                                          'read_local_addr_fifo']),
                                                self.addrwidth)
        self.read_local_stride_fifo = self.m.Wire('_'.join(['', self.name,
                                                            'read_local_stride_fifo']),
                                                  self.addrwidth)
        self.read_local_size_fifo = self.m.Wire('_'.join(['', self.name,
                                                          'read_local_size_fifo']),
                                                self.addrwidth + 1)

        read_unpack_values = self.unpack_read_req(self.read_req_fifo.rdata)
        self.read_op_sel_fifo.assign(read_unpack_values[0])
        self.read_local_addr_fifo.assign(read_unpack_values[1])
        self.read_local_stride_fifo.assign(read_unpack_values[2])
        self.read_local_size_fifo.assign(read_unpack_values[3])

        self.read_op_sel_buf = self.m.Reg('_'.join(['', self.name,
                                                    'read_op_sel_buf']),
                                          self.op_sel_width, initval=0)
        self.read_local_addr_buf = self.m.Reg('_'.join(['', self.name,
                                                        'read_local_addr_buf']),
                                              self.addrwidth, initval=0)
        self.read_local_stride_buf = self.m.Reg('_'.join(['', self.name,
                                                          'read_local_stride_buf']),
                                                self.addrwidth, initval=0)
        self.read_local_size_buf = self.m.Reg('_'.join(['', self.name,
                                                        'read_local_size_buf']),
                                              self.addrwidth + 1, initval=0)

        self.read_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'read_data_busy']), initval=0)
        self.read_data_idle = self.m.Wire('_'.join(['', self.name, 'read_data_idle']))
        self.read_idle = self.m.Wire('_'.join(['', self.name, 'read_idle']))

        self.read_data_idle.assign(vtypes.Ands(self.read_req_fifo.empty,
                                               vtypes.Not(self.read_data_busy)))
        self.read_idle.assign(self.read_data_idle)

        self.read_op_id_map = OrderedDict()
        self.read_op_id_count = 1
        self.read_ops = []

        self.read_data_fsm = None
        self.read_data_narrow_fsm = None
        self.read_data_wide_fsm = None

    def read(self, fsm):
        # state 0
        self.seq.If(fsm.here, self.read_idle)(
            self.read_data_busy(1)
        )
        fsm.If(self.read_idle).goto_next()

        # state 1
        rcond = fsm.here
        tdata = self.m.TmpReg(self.datawidth, initval=0,
                              signed=True, prefix='axistreamin_tdata')
        if self.tdata.tlast is not None:
            tlast = self.m.TmpReg(initval=0,
                                  prefix='axistreamin_tlast')
        else:
            tlast = None

        _ = self.read_data(cond=rcond)
        fsm.If(self.tdata.tvalid)(
            tdata(self.tdata.tdata),
        )
        if self.tdata.tlast is not None:
            fsm.If(self.tdata.tvalid)(
                tlast(self.tdata.tlast),
            )
        self.seq.If(fsm.here, self.tdata.tvalid)(
            self.read_data_busy(0)
        )
        fsm.If(self.tdata.tvalid).goto_next()

        return tdata, tlast

    def dma_read(self, fsm, ram, local_addr, size,
                 local_stride=1, port=0):

        self._dma_read(fsm, ram, local_addr, size,
                       local_stride, port)

        self.dma_wait_read(fsm)

    def dma_read_async(self, fsm, ram, local_addr, size,
                       local_stride=1, port=0):

        self._dma_read(fsm, ram, local_addr, size,
                       local_stride, port)

    def dma_wait_read(self, fsm):

        fsm.If(self.read_idle).goto_next()

    def _dma_read(self, fsm, ram, local_addr, size,
                  local_stride=1, port=0, ram_method=None):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, (RAM, MultibankRAM)):
            raise TypeError('RAM object is required.')

        if ram_method is None:
            ram_method = getattr(ram, 'write_burst')

        ram_method_name = (ram_method.func.__name__
                           if isinstance(ram_method, functools.partial) else
                           ram_method.__name__)
        ram_datawidth = (ram.packed_datawidth if 'packed' in ram_method_name else
                         ram.rams[0].packed_datawidth if 'block' in ram_method_name else
                         ram.datawidth)

        if not isinstance(self.datawidth, int):
            raise TypeError("axi.datawidth must be int, not '%s'" %
                            str(type(self.datawidth)))

        if not isinstance(ram_datawidth, int):
            raise TypeError("ram_datawidth must be int, not '%s'" %
                            str(type(ram_datawidth)))

        start = fsm.here

        self._set_read_request(ram, port, ram_method, ram_datawidth,
                               start, local_addr, size, local_stride)
        self._synthesize_read_data_fsm(ram, port, ram_method, ram_datawidth)

        fsm.If(vtypes.Not(self.read_req_fifo.almost_full)).goto_next()

    def _set_read_request(self, ram, port, ram_method, ram_datawidth,
                          start, local_addr, size, local_stride):

        local_size = size
        op_id = self._get_read_op_id(ram, port, ram_method)

        enq_cond = vtypes.Ands(start,
                               vtypes.Not(self.read_req_fifo.almost_full))

        _ = self.read_req_fifo.enq_rtl(self.pack_read_req(op_id,
                                                          local_addr,
                                                          local_stride,
                                                          local_size),
                                       cond=enq_cond)

    def _synthesize_read_data_fsm(self, ram, port, ram_method, ram_datawidth):

        if self.datawidth == ram_datawidth:
            return self._synthesize_read_data_fsm_same(ram, port, ram_method, ram_datawidth)

        if self.datawidth < ram_datawidth:
            return self._synthesize_read_data_fsm_narrow(ram, port, ram_method, ram_datawidth)

        return self._synthesize_read_data_fsm_wide(ram, port, ram_method, ram_datawidth)

    def _synthesize_read_data_fsm_same(self, ram, port, ram_method, ram_datawidth):

        op_id = self._get_read_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_fsm is not None:
            """ new op """
            data_fsm = self.read_data_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_addr_buf(self.read_local_addr_fifo),
            self.read_local_stride_buf(self.read_local_stride_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.read_op_sel_buf == op_id)
        ram_method(self.read_local_addr_buf, self.read_local_stride_buf,
                   self.read_local_size_buf, 1,
                   self.tdata.tdata, self.tdata.tvalid, False,
                   port=port, cond=ram_cond)
        data_fsm.goto_next()

        # Data state 2
        _ = self.read_data(cond=data_fsm)
        self.seq.If(data_fsm.here, self.tdata.tvalid)(
            self.read_local_size_buf.dec()
        )

        data_fsm.If(self.tdata.tvalid, self.read_local_size_buf <= 1).goto_init()
        self.seq.If(data_fsm.here, self.tdata.tvalid, self.read_local_size_buf <= 1)(
            self.read_data_busy(0)
        )

    def _synthesize_read_data_fsm_narrow(self, ram, port, ram_method, ram_datawidth):
        """ axi.datawidth < ram.datawidth """

        if ram_datawidth % self.datawidth != 0:
            raise ValueError(
                'ram_datawidth must be multiple number of axi.datawidth')

        op_id = self._get_read_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)
        pack_size = ram_datawidth // self.datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_narrow_fsm is not None:
            """ new op """
            data_fsm = self.read_data_narrow_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_narrow_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_narrow_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_addr_buf(self.read_local_addr_fifo),
            self.read_local_stride_buf(self.read_local_stride_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.read_op_sel_buf == op_id)
        wdata = self.m.TmpReg(ram_datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'read_narrow_wdata']))
        wvalid = self.m.TmpReg(initval=0, prefix='_'.join(['', self.name, 'read_narrow_wvalid']))
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'read_narrow_count']))
        ram_method(self.read_local_addr_buf, self.read_local_stride_buf,
                   self.read_local_size_buf, 1,
                   wdata, wvalid, False,
                   port=port, cond=ram_cond)
        data_fsm(
            count(0),
            wvalid(0)
        )
        data_fsm.goto_next()

        # Data state 2
        _ = self.read_data(cond=data_fsm)
        cond = self.read_op_sel_buf == op_id

        data_fsm.If(cond)(
            wvalid(0)
        )
        data_fsm.If(cond, self.tdata.tvalid, count < pack_size - 1)(
            count.inc(),
            wdata(vtypes.Cat(self.tdata.tdata, wdata[self.datawidth:])),
            wvalid(0),
        )
        data_fsm.If(cond, self.tdata.tvalid, count == pack_size - 1)(
            count(0),
            wdata(vtypes.Cat(self.tdata.tdata, wdata[self.datawidth:])),
            wvalid(1)
        )
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, count == pack_size - 1)(
            self.read_local_size_buf.dec()
        )

        data_fsm.If(cond, self.tdata.tvalid, self.read_local_size_buf <= 1,
                    count == pack_size - 1).goto_init()
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, self.read_local_size_buf <= 1,
                    count == pack_size - 1)(
            self.read_data_busy(0)
        )

    def _synthesize_read_data_fsm_wide(self, ram, port, ram_method, ram_datawidth):
        """ axi.datawidth > ram.datawidth """

        if self.datawidth % ram_datawidth != 0:
            raise ValueError(
                'axi.datawidth must be multiple number of ram_datawidth')

        op_id = self._get_read_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)
        pack_size = self.datawidth // ram_datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_wide_fsm is not None:
            """ new op """
            data_fsm = self.read_data_wide_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_wide_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_wide_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_addr_buf(self.read_local_addr_fifo),
            self.read_local_stride_buf(self.read_local_stride_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.read_op_sel_buf == op_id)
        wdata = self.m.TmpReg(self.datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'read_wide_wdata']))
        wvalid = self.m.TmpReg(initval=0, prefix='_'.join(['', self.name, 'read_wide_wvalid']))
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'read_wide_count']))
        _wdata = wdata[:ram_datawidth]
        ram_method(self.read_local_addr_buf, self.read_local_stride_buf,
                   self.read_local_size_buf, 1,
                   _wdata, wvalid, False,
                   port=port, cond=ram_cond)
        data_fsm(
            count(0),
            wvalid(0)
        )
        data_fsm.goto_next()

        # Data state 2
        cond = self.read_op_sel_buf == op_id
        rcond = vtypes.Ands(data_fsm.here, cond, count == 0)
        _ = self.read_data(cond=rcond)
        data_fsm.If(cond)(
            wvalid(0)
        )
        data_fsm.If(cond, self.tdata.tvalid, count == 0)(
            count.inc(),
            wdata(self.tdata.tdata),
            wvalid(1),
        )
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, count == 0)(
            self.read_local_size_buf.dec()
        )
        data_fsm.If(cond, count > 0)(
            count.inc(),
            wdata(wdata >> ram_datawidth),
            wvalid(1),
        )
        self.seq.If(data_fsm.here, cond, count > 0)(
            self.read_local_size_buf.dec()
        )
        data_fsm.If(cond, count == pack_size - 1)(
            count(0)
        )

        data_fsm.If(self.read_local_size_buf <= 1,
                    cond, count > 0).goto_init()
        data_fsm.If(self.read_local_size_buf <= 1,
                    cond, self.tdata.tvalid, count == 0).goto_init()
        self.seq.If(data_fsm.here, self.read_local_size_buf <= 1,
                    cond, count > 0)(
            self.read_data_busy(0)
        )
        self.seq.If(data_fsm.here, self.read_local_size_buf <= 1,
                    cond, self.tdata.tvalid, count == 0)(
            self.read_data_busy(0)
        )

    def _set_flag(self, fsm, prefix='axistreamin_flag'):
        flag = self.m.TmpWire(prefix=prefix)
        flag.assign(fsm.here)
        return flag

    def _get_read_op_id(self, ram, port, ram_method):

        ram_id = ram._id()
        port = vtypes.to_int(port)
        ram_method_name = (ram_method.func.__name__
                           if isinstance(ram_method, functools.partial) else
                           ram_method.__name__)
        op = (ram_id, port, ram_method_name)

        if op in self.read_op_id_map:
            op_id = self.read_op_id_map[op]
        else:
            op_id = self.read_op_id_count
            self.read_op_id_count += 1
            self.read_op_id_map[op] = op_id

        return op_id

    def pack_read_req(self, op_sel, local_addr, local_stride, local_size):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_read_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='pack_read_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='pack_read_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_read_req_local_size')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth * 3 + 1,
                                prefix='pack_read_req_packed')
        packed.assign(vtypes.Cat(_op_sel, _local_addr, _local_stride, _local_size))
        return packed

    def unpack_read_req(self, v):
        op_sel = v[self.addrwidth * 3 + 1:self.addrwidth * 3 + 1 + self.op_sel_width]
        local_addr = v[self.addrwidth * 2 + 1:self.addrwidth * 2 + 1 + self.addrwidth]
        local_stride = v[self.addrwidth + 1:self.addrwidth + 1 + self.addrwidth]
        local_size = v[0:self.addrwidth + 1]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_read_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='unpack_read_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='unpack_read_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_read_req_local_size')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        return _op_sel, _local_addr, _local_stride, _local_size


class AXIStreamInFifo(AXIStreamIn):
    """ AXI Stream Interface to FIFO for Input """

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 with_last=True, with_strb=False,
                 id_width=0, user_width=0, dest_width=0,
                 noio=False,
                 op_sel_width=8, req_fifo_addrwidth=3, fsm_as_module=False):

        axi.AxiStreamIn.__init__(self, m, name, clk, rst, datawidth,
                                 with_last, with_strb,
                                 id_width, user_width, dest_width,
                                 noio)

        self.addrwidth = addrwidth

        self.op_sel_width = op_sel_width
        self.req_fifo_addrwidth = req_fifo_addrwidth
        self.fsm_as_module = fsm_as_module

        self.mutex = None

        # Read
        self.read_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'read_req_fifo']),
                                  self.clk, self.rst,
                                  datawidth=self.op_sel_width + self.addrwidth + 1,
                                  addrwidth=self.req_fifo_addrwidth,
                                  sync=False)

        self.read_op_sel_fifo = self.m.Wire('_'.join(['', self.name,
                                                      'read_op_sel_fifo']),
                                            self.op_sel_width)
        self.read_local_size_fifo = self.m.Wire('_'.join(['', self.name,
                                                          'read_local_size_fifo']),
                                                self.addrwidth + 1)

        read_unpack_values = self.unpack_read_req(self.read_req_fifo.rdata)
        self.read_op_sel_fifo.assign(read_unpack_values[0])
        self.read_local_size_fifo.assign(read_unpack_values[1])

        self.read_op_sel_buf = self.m.Reg('_'.join(['', self.name,
                                                    'read_op_sel_buf']),
                                          self.op_sel_width, initval=0)
        self.read_local_size_buf = self.m.Reg('_'.join(['', self.name,
                                                        'read_local_size_buf']),
                                              self.addrwidth + 1, initval=0)

        self.read_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'read_data_busy']), initval=0)
        self.read_data_idle = self.m.Wire('_'.join(['', self.name, 'read_data_idle']))
        self.read_idle = self.m.Wire('_'.join(['', self.name, 'read_idle']))

        self.read_data_idle.assign(vtypes.Ands(self.read_req_fifo.empty,
                                               vtypes.Not(self.read_data_busy)))
        self.read_idle.assign(self.read_data_idle)

        self.read_op_id_map = OrderedDict()
        self.read_op_id_count = 1
        self.read_ops = []

        self.read_data_fsm = None
        self.read_data_narrow_fsm = None
        self.read_data_wide_fsm = None

    def dma_read(self, fsm, fifo, size):

        self._dma_read(fsm, fifo, size)

        self.dma_wait_read(fsm)

    def dma_read_async(self, fsm, fifo, size):

        self._dma_read(fsm, fifo, size)

    def dma_wait_read(self, fsm):

        fsm.If(self.read_idle).goto_next()

    def _dma_read(self, fsm, fifo, size):

        if not isinstance(fifo, FIFO):
            raise TypeError('FIFO object is required.')

        start = fsm.here

        fifo_datawidth = fifo.datawidth

        if not isinstance(self.datawidth, int):
            raise TypeError("axi.datawidth must be int, not '%s'" %
                            str(type(self.datawidth)))

        if not isinstance(fifo_datawidth, int):
            raise TypeError("fifo_datawidth must be int, not '%s'" %
                            str(type(fifo_datawidth)))

        self._set_read_request(fifo, start, size)
        self._synthesize_read_data_fsm(fifo, fifo_datawidth)

        fsm.If(vtypes.Not(self.read_req_fifo.almost_full)).goto_next()

    def _set_read_request(self, fifo, start, size):

        local_size = size
        op_id = self._get_read_op_id(fifo)

        enq_cond = vtypes.Ands(start,
                               vtypes.Not(self.read_req_fifo.almost_full))

        _ = self.read_req_fifo.enq_rtl(self.pack_read_req(op_id,
                                                          local_size),
                                       cond=enq_cond)

    def _synthesize_read_data_fsm(self, fifo, fifo_datawidth):

        if self.datawidth == fifo_datawidth:
            return self._synthesize_read_data_fsm_same(fifo, fifo_datawidth)

        if self.datawidth < fifo_datawidth:
            return self._synthesize_read_data_fsm_narrow(fifo, fifo_datawidth)

        return self._synthesize_read_data_fsm_wide(fifo, fifo_datawidth)

    def _synthesize_read_data_fsm_same(self, fifo, fifo_datawidth):

        op_id = self._get_read_op_id(fifo)

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_fsm is not None:
            """ new op """
            data_fsm = self.read_data_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        read_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.almost_full),
                                self.read_op_sel_buf == op_id)
        _ = self.read_data(cond=read_cond)

        self.seq.If(data_fsm.here, self.tdata.tvalid, vtypes.Not(fifo.almost_full))(
            self.read_local_size_buf.dec()
        )

        fifo_cond = vtypes.Ands(data_fsm.here, self.tdata.tvalid,
                                vtypes.Not(fifo.almost_full), self.read_op_sel_buf == op_id)
        fifo.enq_rtl(self.tdata.tdata, cond=fifo_cond)

        data_fsm.If(self.tdata.tvalid, vtypes.Not(fifo.almost_full),
                    self.read_local_size_buf <= 1).goto_init()

        self.seq.If(data_fsm.here, self.tdata.tvalid, vtypes.Not(fifo.almost_full),
                    self.read_local_size_buf <= 1)(
            self.read_data_busy(0)
        )

    def _synthesize_read_data_fsm_narrow(self, fifo, fifo_datawidth):
        """ axi.datawidth < fifo.datawidth """

        if fifo_datawidth % self.datawidth != 0:
            raise ValueError(
                'fifo_datawidth must be multiple number of axi.datawidth')

        op_id = self._get_read_op_id(fifo)
        pack_size = fifo_datawidth // self.datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_narrow_fsm is not None:
            """ new op """
            data_fsm = self.read_data_narrow_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_narrow_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_narrow_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)

        wdata = self.m.TmpReg(fifo_datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'read_narrow_wdata']))
        wvalid = self.m.TmpReg(initval=0, prefix='_'.join(['', self.name, 'read_narrow_wvalid']))
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'read_narrow_count']))
        data_fsm(
            count(0),
            wvalid(0)
        )
        data_fsm.If(cond).goto_next()

        # Data state 1
        read_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.almost_full),
                                self.read_op_sel_buf == op_id)
        _ = self.read_data(cond=read_cond)

        cond = vtypes.Ands(vtypes.Not(fifo.almost_full), self.read_op_sel_buf == op_id)

        data_fsm.If(cond)(
            wvalid(0)
        )
        data_fsm.If(cond, self.tdata.tvalid, count < pack_size - 1)(
            count.inc(),
            wdata(vtypes.Cat(self.tdata.tdata, wdata[self.datawidth:])),
            wvalid(0),
        )
        data_fsm.If(cond, self.tdata.tvalid, count == pack_size - 1)(
            count(0),
            wdata(vtypes.Cat(self.tdata.tdata, wdata[self.datawidth:])),
            wvalid(1)
        )
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, count == pack_size - 1)(
            self.read_local_size_buf.dec()
        )

        fifo_cond = wvalid
        fifo.enq_rtl(wdata, cond=fifo_cond)

        data_fsm.If(cond, self.tdata.tvalid, self.read_local_size_buf <= 1,
                    count == pack_size - 1).goto_init()
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, self.read_local_size_buf <= 1,
                    count == pack_size - 1)(
            self.read_data_busy(0)
        )

    def _synthesize_read_data_fsm_wide(self, fifo, fifo_datawidth):
        """ axi.datawidth > fifo.datawidth """

        if self.datawidth % fifo_datawidth != 0:
            raise ValueError(
                'axi.datawidth must be multiple number of fifo_datawidth')

        op_id = self._get_read_op_id(fifo)
        pack_size = self.datawidth // fifo_datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.read_ops:
            """ already synthesized op """
            return

        self.read_ops.append(op_id)

        # Data FSM
        if self.read_data_wide_fsm is not None:
            """ new op """
            data_fsm = self.read_data_wide_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'read_data_wide_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.read_data_wide_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.read_data_busy),
                           vtypes.Not(self.read_req_fifo.empty),
                           self.read_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.read_data_busy(1),
            self.read_op_sel_buf(self.read_op_sel_fifo),
            self.read_local_size_buf(self.read_local_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)

        wdata = self.m.TmpReg(self.datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'read_wide_wdata']))
        wvalid = self.m.TmpReg(initval=0, prefix='_'.join(['', self.name, 'read_wide_wvalid']))
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'read_wide_count']))
        data_fsm(
            count(0),
            wvalid(0)
        )
        data_fsm.If(cond).goto_next()

        # Data state 1
        read_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.almost_full),
                                self.read_op_sel_buf == op_id, count == 0)
        _ = self.read_data(cond=read_cond)

        cond = vtypes.Ands(vtypes.Not(fifo.almost_full),
                           self.read_op_sel_buf == op_id)

        data_fsm.If(cond)(
            wvalid(0)
        )
        data_fsm.If(cond, self.tdata.tvalid, count == 0)(
            count.inc(),
            wdata(self.tdata.tdata),
            wvalid(1),
        )
        self.seq.If(data_fsm.here, cond, self.tdata.tvalid, count == 0)(
            self.read_local_size_buf.dec()
        )
        data_fsm.If(cond, count > 0)(
            count.inc(),
            wdata(wdata >> fifo_datawidth),
            wvalid(1),
        )
        self.seq.If(data_fsm.here, cond, count > 0)(
            self.read_local_size_buf.dec()
        )
        data_fsm.If(cond, count == pack_size - 1)(
            count(0)
        )

        fifo_wdata = self.m.TmpWire(fifo_datawidth,
                                    prefix='_'.join(['', self.name, 'read_wide_fifo_wdata']))
        fifo_wdata.assign(wdata)
        fifo_cond = wvalid
        fifo.enq_rtl(fifo_wdata, cond=fifo_cond)

        data_fsm.If(self.read_local_size_buf <= 1,
                    cond, count == pack_size - 1).goto_init()
        self.seq.If(data_fsm.here, self.read_local_size_buf <= 1,
                    cond, count == pack_size - 1)(
            self.read_data_busy(0)
        )

    def _get_read_op_id(self, fifo):

        fifo_id = fifo._id()
        op = fifo_id

        if op in self.read_op_id_map:
            op_id = self.read_op_id_map[op]
        else:
            op_id = self.read_op_id_count
            self.read_op_id_count += 1
            self.read_op_id_map[op] = op_id

        return op_id

    def pack_read_req(self, op_sel, local_size):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_read_req_op_sel')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_read_req_local_size')
        _op_sel.assign(op_sel)
        _local_size.assign(local_size)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth + 1,
                                prefix='pack_read_req_packed')
        packed.assign(vtypes.Cat(_op_sel, _local_size))
        return packed

    def unpack_read_req(self, v):
        op_sel = v[self.addrwidth + 1:self.addrwidth + 1 + self.op_sel_width]
        local_size = v[0:self.addrwidth + 1]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_read_req_op_sel')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_read_req_local_size')
        _op_sel.assign(op_sel)
        _local_size.assign(local_size)
        return _op_sel, _local_size
