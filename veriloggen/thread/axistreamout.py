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


class AXIStreamOut(axi.AxiStreamOut, _MutexFunction):
    """ AXI Stream Interface for Output """

    __intrinsics__ = {'write': 'write',
                      'dma_write': 'dma_write',
                      'dma_write_async': 'dma_write_async',
                      'dma_wait_write': 'dma_wait_write',
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 with_last=True, with_strb=False,
                 id_width=0, user_width=0, dest_width=0,
                 noio=False,
                 op_sel_width=8, req_fifo_addrwidth=3, fsm_as_module=False):

        axi.AxiStreamOut.__init__(self, m, name, clk, rst, datawidth,
                                  with_last, with_strb,
                                  id_width, user_width, dest_width,
                                  noio)

        self.addrwidth = addrwidth

        self.op_sel_width = op_sel_width
        self.req_fifo_addrwidth = req_fifo_addrwidth
        self.fsm_as_module = fsm_as_module

        self.mutex = None

        # Write
        self.write_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'write_req_fifo']),
                                   self.clk, self.rst,
                                   datawidth=self.op_sel_width + self.addrwidth * 3 + 1,
                                   addrwidth=self.req_fifo_addrwidth,
                                   sync=False)

        self.write_op_sel_fifo = self.m.Wire('_'.join(['', self.name,
                                                       'write_op_sel_fifo']),
                                             self.op_sel_width)
        self.write_local_addr_fifo = self.m.Wire('_'.join(['', self.name,
                                                           'write_local_addr_fifo']),
                                                 self.addrwidth)
        self.write_local_stride_fifo = self.m.Wire('_'.join(['', self.name,
                                                             'write_local_stride_fifo']),
                                                   self.addrwidth)
        self.write_size_fifo = self.m.Wire('_'.join(['', self.name,
                                                     'write_size_fifo']),
                                           self.addrwidth + 1)

        write_unpack_values = self.unpack_write_req(self.write_req_fifo.rdata)
        self.write_op_sel_fifo.assign(write_unpack_values[0])
        self.write_local_addr_fifo.assign(write_unpack_values[1])
        self.write_local_stride_fifo.assign(write_unpack_values[2])
        self.write_size_fifo.assign(write_unpack_values[3])

        self.write_op_sel_buf = self.m.Reg('_'.join(['', self.name,
                                                     'write_op_sel_buf']),
                                           self.op_sel_width, initval=0)
        self.write_local_addr_buf = self.m.Reg('_'.join(['', self.name,
                                                         'write_local_addr_buf']),
                                               self.addrwidth, initval=0)
        self.write_local_stride_buf = self.m.Reg('_'.join(['', self.name,
                                                           'write_local_stride_buf']),
                                                 self.addrwidth, initval=0)
        self.write_size_buf = self.m.Reg('_'.join(['', self.name,
                                                   'write_size_buf']),
                                         self.addrwidth + 1, initval=0)

        self.write_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'write_data_busy']), initval=0)
        self.write_data_idle = self.m.Wire('_'.join(['', self.name, 'write_data_idle']))
        self.write_idle = self.m.Wire('_'.join(['', self.name, 'write_idle']))

        self.write_data_idle.assign(vtypes.Ands(self.write_req_fifo.empty,
                                                vtypes.Not(self.write_data_busy)))
        self.write_idle.assign(self.write_data_idle)

        self.write_op_id_map = OrderedDict()
        self.write_op_id_count = 1
        self.write_ops = []

        self.write_data_fsm = None
        self.write_data_narrow_fsm = None
        self.write_data_wide_fsm = None

    def write(self, fsm, value, last=False):
        # state 0
        self.seq.If(fsm.here, self.write_idle)(
            self.write_data_busy(1)
        )
        fsm.If(self.write_idle).goto_next()

        # state 1
        wcond = fsm.here
        wdata = value
        wlast = last
        _ = self.write_data(wdata, wlast, cond=wcond)
        ack = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))
        self.seq.If(fsm.here, ack)(
            self.write_data_busy(0)
        )
        fsm.If(ack).goto_next()

    def write_fence(self, fsm, value, last=False):

        self.write(fsm, value, last)

        accept = vtypes.Ors(vtypes.Ands(self.tdata.tready, self.tdata.tvalid),
                            vtypes.Not(self.tdata.tvalid))

        fsm.If(accept).goto_next()

    def dma_write(self, fsm, ram, local_addr, size,
                  local_stride=1, port=0):

        self._dma_write(fsm, ram, local_addr, size,
                        local_stride, port)

        self.dma_wait_write(fsm)

    def dma_write_async(self, fsm, ram, local_addr, size,
                        local_stride=1, port=0):

        self._dma_write(fsm, ram, local_addr, size,
                        local_stride, port)

    def dma_wait_write(self, fsm):

        fsm.If(self.write_idle).goto_next()

    def _dma_write(self, fsm, ram, local_addr, size,
                   local_stride=1, port=0, ram_method=None):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, (RAM, MultibankRAM)):
            raise TypeError('RAM object is required.')

        if ram_method is None:
            ram_method = getattr(ram, 'read_burst')

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

        self._set_write_request(ram, port, ram_method, ram_datawidth,
                                start, local_addr, size, local_stride)
        self._synthesize_write_data_fsm(ram, port, ram_method, ram_datawidth)

        fsm.If(vtypes.Not(self.write_req_fifo.almost_full)).goto_next()

    def _set_write_request(self, ram, port, ram_method, ram_datawidth,
                           start, local_addr, size, local_stride):

        local_size = size
        op_id = self._get_write_op_id(ram, port, ram_method)

        enq_cond = vtypes.Ands(start,
                               vtypes.Not(self.write_req_fifo.almost_full))

        _ = self.write_req_fifo.enq_rtl(self.pack_write_req(op_id,
                                                            local_addr,
                                                            local_stride,
                                                            local_size),
                                        cond=enq_cond)

    def _synthesize_write_data_fsm(self, ram, port, ram_method, ram_datawidth):

        if self.datawidth == ram_datawidth:
            return self._synthesize_write_data_fsm_same(ram, port, ram_method, ram_datawidth)

        if self.datawidth < ram_datawidth:
            return self._synthesize_write_data_fsm_narrow(ram, port, ram_method, ram_datawidth)

        return self._synthesize_write_data_fsm_wide(ram, port, ram_method, ram_datawidth)

    def _synthesize_write_data_fsm_same(self, ram, port, ram_method, ram_datawidth):

        op_id = self._get_write_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        self.write_ops.append(op_id)

        # Data FSM
        if self.write_data_fsm is not None:
            """ new op """
            data_fsm = self.write_data_fsm
            data_fsm.set_index(1)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            self.write_local_addr_buf(self.write_local_addr_fifo),
            self.write_local_stride_buf(self.write_local_stride_fifo),
            self.write_size_buf(self.write_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        rready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, 1,
            rready, port=port, cond=ram_cond)
        data_fsm.goto_next()

        # Data state 2
        wcond = vtypes.Ands(self.write_op_sel_buf == op_id, rvalid, rready)
        _ = self.write_data(rdata, rlast, cond=wcond)
        self.seq.If(data_fsm.here, wcond)(
            self.write_size_buf.dec()
        )

        data_fsm.If(wcond, rlast).goto_init()
        self.seq.If(data_fsm.here, wcond, rlast)(
            self.write_data_busy(0)
        )

    def _synthesize_write_data_fsm_narrow(self, ram, port, ram_method, ram_datawidth):
        """ axi.datawidth < ram.datawidth """

        if ram_datawidth % self.datawidth != 0:
            raise ValueError(
                'ram_datawidth must be multiple number of axi.datawidth')

        op_id = self._get_write_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)
        pack_size = ram_datawidth // self.datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        # Data FSM
        if self.write_data_narrow_fsm is not None:
            """ new op """
            data_fsm = self.write_data_narrow_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_narrow_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_narrow_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            self.write_local_addr_buf(self.write_local_addr_fifo),
            self.write_local_stride_buf(self.write_local_stride_fifo),
            # self.write_size_fifo: local_size
            self.write_size_buf(self.write_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        self.seq.If(data_fsm.here)(
            # local_size -> global_size
            self.write_size_buf(self.write_size_buf << log_pack_size),
        )

        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_count']))
        rready = vtypes.Ands(vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid)),
                             count == 0)
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, 1,
            rready, port=port, cond=ram_cond)

        data_fsm(
            count(0)
        )
        data_fsm.goto_next()

        # Data state 2
        wdata = self.m.TmpReg(ram_datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wdata']))
        wlast = self.m.TmpReg(initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wlast']))
        wack = vtypes.Ands(vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid)),
                           self.write_size_buf > 0)
        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id, wack,
                            vtypes.Ors(count > 0, rvalid))
        _wdata = vtypes.Mux(count == 0, rdata[:self.datawidth], wdata[:self.datawidth])
        _wlast = self.write_size_buf == 1
        _ = self.write_data(_wdata, _wlast, cond=wcond)

        self.seq.If(data_fsm.here, wcond)(
            self.write_size_buf.dec()
        )

        data_fsm.If(wcond, count == 0)(
            wdata(rdata[self.datawidth:]),
            wlast(rlast),
            count.inc(),
        )
        data_fsm.If(wcond, count > 0)(
            wdata(wdata >> self.datawidth),
            count.inc(),
        )
        data_fsm.If(wcond, count == pack_size - 1)(
            count(0)
        )

        data_fsm.If(wcond, count == pack_size - 1, wlast).goto_init()

        self.seq.If(data_fsm.here, wcond, count == pack_size - 1, wlast)(
            self.write_data_busy(0)
        )

    def _synthesize_write_data_fsm_wide(self, ram, port, ram_method, ram_datawidth):
        """ axi.datawidth > ram.datawidth """

        if self.datawidth % ram_datawidth != 0:
            raise ValueError(
                'axi.datawidth must be multiple number of ram_datawidth')

        op_id = self._get_write_op_id(ram, port, ram_method)
        port = vtypes.to_int(port)
        pack_size = self.datawidth // ram_datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        self.write_ops.append(op_id)

        # Data FSM
        if self.write_data_wide_fsm is not None:
            """ new op """
            data_fsm = self.write_data_wide_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_wide_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_wide_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        res = vtypes.Mux(
            vtypes.And(self.write_size_fifo, 2 ** log_pack_size - 1) > 0, 1, 0)
        global_size = (self.write_size_fifo >> log_pack_size) + res
        local_size = global_size << log_pack_size

        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            self.write_local_addr_buf(self.write_local_addr_fifo),
            self.write_local_stride_buf(self.write_local_stride_fifo),
            self.write_size_buf(local_size),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_count']))
        rready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid), count > 0)
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, 1,
            rready, port=port, cond=ram_cond)

        data_fsm(
            count(0)
        )
        data_fsm.goto_next()

        # Data state 2
        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id,
                            count == pack_size - 1, rvalid, rready)
        wdata = self.m.TmpReg(self.datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_wdata']))
        _wdata = vtypes.Cat(rdata, wdata[ram_datawidth:self.datawidth])
        _wlast = vtypes.Ors(rlast, self.write_size_buf <= 1)
        _ = self.write_data(_wdata, _wlast, cond=wcond)

        self.seq.If(data_fsm.here, rvalid, rready)(
            self.write_size_buf.dec()
        )
        data_fsm.If(rvalid, rready)(
            wdata(_wdata),
            count.inc(),
        )
        data_fsm.If(rvalid, rready, count == pack_size - 1)(
            count(0)
        )
        data_fsm.If(count == pack_size - 1, rvalid, rready, rlast).goto_init()

        self.seq.If(data_fsm.here, count == pack_size - 1, rvalid, rready, rlast)(
            self.write_data_busy(0)
        )

    def _set_flag(self, fsm, prefix='axistreamout_flag'):
        flag = self.m.TmpWire(prefix=prefix)
        flag.assign(fsm.here)
        return flag

    def _get_write_op_id(self, ram, port, ram_method):

        ram_id = ram._id()
        port = vtypes.to_int(port)
        ram_method_name = (ram_method.func.__name__
                           if isinstance(ram_method, functools.partial) else
                           ram_method.__name__)
        op = (ram_id, port, ram_method_name)

        if op in self.write_op_id_map:
            op_id = self.write_op_id_map[op]
        else:
            op_id = self.write_op_id_count
            self.write_op_id_count += 1
            self.write_op_id_map[op] = op_id

        return op_id

    def pack_write_req(self, op_sel, local_addr, local_stride, local_size):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_write_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='pack_write_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='pack_write_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_write_req_local_size')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth * 3 + 1,
                                prefix='pack_write_req_packed')
        packed.assign(vtypes.Cat(_op_sel, _local_addr, _local_stride, _local_size))
        return packed

    def unpack_write_req(self, v):
        op_sel = v[self.addrwidth * 3 + 1:self.addrwidth * 3 + 1 + self.op_sel_width]
        local_addr = v[self.addrwidth * 2 + 1:self.addrwidth * 2 + 1 + self.addrwidth]
        local_stride = v[self.addrwidth + 1:self.addrwidth + 1 + self.addrwidth]
        local_size = v[0:self.addrwidth + 1]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_write_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='unpack_write_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='unpack_write_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_write_req_local_size')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        return _op_sel, _local_addr, _local_stride, _local_size


class AXIStreamOutFifo(AXIStreamOut):
    """ AXI Stream Interface from FIFO for Output """

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 with_last=True, with_strb=False,
                 id_width=0, user_width=0, dest_width=0,
                 noio=False,
                 op_sel_width=8, req_fifo_addrwidth=3, fsm_as_module=False):

        axi.AxiStreamOut.__init__(self, m, name, clk, rst, datawidth,
                                  with_last, with_strb,
                                  id_width, user_width, dest_width,
                                  noio)

        self.addrwidth = addrwidth

        self.op_sel_width = op_sel_width
        self.req_fifo_addrwidth = req_fifo_addrwidth
        self.fsm_as_module = fsm_as_module

        self.mutex = None

        # Write
        self.write_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'write_req_fifo']),
                                   self.clk, self.rst,
                                   datawidth=self.op_sel_width + self.addrwidth + 1,
                                   addrwidth=self.req_fifo_addrwidth,
                                   sync=False)

        self.write_op_sel_fifo = self.m.Wire('_'.join(['', self.name,
                                                       'write_op_sel_fifo']),
                                             self.op_sel_width)
        self.write_size_fifo = self.m.Wire('_'.join(['', self.name,
                                                     'write_size_fifo']),
                                           self.addrwidth + 1)

        write_unpack_values = self.unpack_write_req(self.write_req_fifo.rdata)
        self.write_op_sel_fifo.assign(write_unpack_values[0])
        self.write_size_fifo.assign(write_unpack_values[1])

        self.write_op_sel_buf = self.m.Reg('_'.join(['', self.name,
                                                     'write_op_sel_buf']),
                                           self.op_sel_width, initval=0)
        self.write_size_buf = self.m.Reg('_'.join(['', self.name,
                                                   'write_size_buf']),
                                         self.addrwidth + 1, initval=0)

        self.write_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'write_data_busy']), initval=0)
        self.write_data_idle = self.m.Wire('_'.join(['', self.name, 'write_data_idle']))
        self.write_idle = self.m.Wire('_'.join(['', self.name, 'write_idle']))

        self.write_data_idle.assign(vtypes.Ands(self.write_req_fifo.empty,
                                                vtypes.Not(self.write_data_busy)))
        self.write_idle.assign(self.write_data_idle)

        self.write_op_id_map = OrderedDict()
        self.write_op_id_count = 1
        self.write_ops = []

        self.write_data_fsm = None
        self.write_data_narrow_fsm = None
        self.write_data_wide_fsm = None

    def dma_write(self, fsm, fifo, size):

        self._dma_write(fsm, fifo, size)

        self.dma_wait_write(fsm)

    def dma_write_async(self, fsm, fifo, size):

        self._dma_write(fsm, fifo, size)

    def dma_wait_write(self, fsm):

        fsm.If(self.write_idle).goto_next()

    def _dma_write(self, fsm, fifo, size):

        if not isinstance(fifo, FIFO):
            raise TypeError('FIFO object is required.')

        start = self._set_flag(fsm)

        fifo_datawidth = fifo.datawidth

        if not isinstance(self.datawidth, int):
            raise TypeError("axi.datawidth must be int, not '%s'" %
                            str(type(self.datawidth)))

        if not isinstance(fifo_datawidth, int):
            raise TypeError("fifo_datawidth must be int, not '%s'" %
                            str(type(fifo_datawidth)))

        self._set_write_request(fifo, start, size)
        self._synthesize_write_data_fsm(fifo, fifo_datawidth)

        fsm.If(vtypes.Not(self.write_req_fifo.almost_full)).goto_next()

    def _set_write_request(self, fifo, start, size):

        local_size = size
        op_id = self._get_write_op_id(fifo)

        enq_cond = vtypes.Ands(start,
                               vtypes.Not(self.write_req_fifo.almost_full))

        _ = self.write_req_fifo.enq_rtl(self.pack_write_req(op_id,
                                                            local_size),
                                        cond=enq_cond)

    def _synthesize_write_data_fsm(self, fifo, fifo_datawidth):

        if self.datawidth == fifo_datawidth:
            return self._synthesize_write_data_fsm_same(fifo, fifo_datawidth)

        if self.datawidth < fifo_datawidth:
            return self._synthesize_write_data_fsm_narrow(fifo, fifo_datawidth)

        return self._synthesize_write_data_fsm_wide(fifo, fifo_datawidth)

    def _synthesize_write_data_fsm_same(self, fifo, fifo_datawidth):

        op_id = self._get_write_op_id(fifo)

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        self.write_ops.append(op_id)

        # Data FSM
        if self.write_data_fsm is not None:
            """ new op """
            data_fsm = self.write_data_fsm
            data_fsm.set_index(1)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            self.write_size_buf(self.write_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        rlast = self.m.TmpReg(prefix='rlast', initval=0)
        data_fsm(
            rlast(0),
        )
        data_fsm.If(cond).goto_next()

        # Data state 1
        cur_rvalid = self.m.TmpWire(prefix='cur_rvalid')
        # rready = vtypes.Ands(vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid)),
        #                     self.write_size_buf > 0)
        rready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))
        deq_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.empty),
                               self.write_op_sel_buf == op_id,
                               self.write_size_buf > 0,
                               rready)
        rdata, rvalid, _ = fifo.deq_rtl(cond=deq_cond)

        wready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))

        repeat_rvalid = self.m.TmpReg(prefix='repeat_rvalid', initval=0)
        self.seq(repeat_rvalid(0))
        self.seq.If(rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        self.seq.If(repeat_rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        cur_rvalid.assign(vtypes.Ors(rvalid, repeat_rvalid))

        data_fsm.If(deq_cond)(
            rlast(self.write_size_buf <= 1)
        )
        self.seq.If(data_fsm.here, deq_cond)(
            self.write_size_buf.dec()
        )

        wcond = vtypes.Ands(self.write_op_sel_buf == op_id, cur_rvalid, wready)
        _ = self.write_data(rdata, rlast, cond=wcond)

        data_fsm.If(wcond, rlast).goto_init()
        self.seq.If(data_fsm.here, wcond, rlast)(
            self.write_data_busy(0)
        )

    def _synthesize_write_data_fsm_narrow(self, fifo, fifo_datawidth):
        """ axi.datawidth < fifo.datawidth """

        if fifo_datawidth % self.datawidth != 0:
            raise ValueError(
                'fifo_datawidth must be multiple number of axi.datawidth')

        op_id = self._get_write_op_id(fifo)
        pack_size = fifo_datawidth // self.datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        # Data FSM
        if self.write_data_narrow_fsm is not None:
            """ new op """
            data_fsm = self.write_data_narrow_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_narrow_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_narrow_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            # self.write_size_fifo: local_size
            self.write_size_buf(self.write_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_count']))
        rlast = self.m.TmpReg(prefix='rlast', initval=0)
        data_fsm(
            count(0),
            rlast(0),
        )
        data_fsm.If(cond).goto_next()

        # Data state 1
        cur_rvalid = self.m.TmpWire(prefix='cur_rvalid')
        # rready = vtypes.Ands(vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid)),
        #                     self.write_size_buf > 0)
        rready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))
        deq_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.empty),
                               self.write_op_sel_buf == op_id,
                               self.write_size_buf > 0,
                               rready,
                               vtypes.Not(cur_rvalid),
                               vtypes.Ors(count == 0, count == pack_size - 1))
        rdata, rvalid, _ = fifo.deq_rtl(cond=deq_cond)

        wready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid))

        repeat_rvalid = self.m.TmpReg(prefix='repeat_rvalid', initval=0)
        self.seq(repeat_rvalid(0))
        self.seq.If(rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        self.seq.If(repeat_rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        cur_rvalid.assign(vtypes.Ors(rvalid, repeat_rvalid))

        data_fsm.If(deq_cond)(
            rlast(self.write_size_buf <= 1)
        )
        self.seq.If(data_fsm.here, deq_cond)(
            self.write_size_buf.dec()
        )

        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id, wready,
                            vtypes.Ors(count > 0, cur_rvalid))
        wdata = self.m.TmpReg(fifo_datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wdata']))
        wlast = self.m.TmpReg(initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wlast']))
        _wdata = vtypes.Mux(count == 0, rdata[:self.datawidth], wdata[:self.datawidth])
        _wlast = vtypes.Ands(self.write_size_buf == 0, count == pack_size - 1)
        _ = self.write_data(_wdata, _wlast, cond=wcond)

        data_fsm.If(wcond, count == 0)(
            wdata(rdata[self.datawidth:]),
            wlast(rlast),
            count.inc()
        )
        data_fsm.If(wcond, count > 0)(
            wdata(wdata >> self.datawidth),
            count.inc()
        )
        data_fsm.If(wcond, count == pack_size - 1)(
            count(0)
        )

        data_fsm.If(wcond, count == pack_size - 1, wlast).goto_init()

        self.seq.If(data_fsm.here, wcond, count == pack_size - 1, wlast)(
            self.write_data_busy(0)
        )

    def _synthesize_write_data_fsm_wide(self, fifo, fifo_datawidth):
        """ axi.datawidth > fifo.datawidth """

        if self.datawidth % fifo_datawidth != 0:
            raise ValueError(
                'axi.datawidth must be multiple number of fifo_datawidth')

        op_id = self._get_write_op_id(fifo)
        pack_size = self.datawidth // fifo_datawidth
        log_pack_size = int(math.log(pack_size, 2))

        if op_id in self.write_ops:
            """ already synthesized op """
            return

        self.write_ops.append(op_id)

        # Data FSM
        if self.write_data_wide_fsm is not None:
            """ new op """
            data_fsm = self.write_data_wide_fsm
            data_fsm.set_index(0)

        else:
            data_fsm = FSM(self.m, '_'.join(['', self.name, 'write_data_wide_fsm']),
                           self.clk, self.rst, as_module=self.fsm_as_module)
            self.write_data_wide_fsm = data_fsm

        # Data state 0
        cond = vtypes.Ands(vtypes.Not(self.write_data_busy),
                           vtypes.Not(self.write_req_fifo.empty),
                           self.write_op_sel_fifo == op_id)
        res = vtypes.Mux(
            vtypes.And(self.write_size_fifo, 2 ** log_pack_size - 1) > 0, 1, 0)
        global_size = (self.write_size_fifo >> log_pack_size) + res
        local_size = global_size << log_pack_size

        self.seq.If(data_fsm.here, cond)(
            self.write_data_busy(1),
            self.write_op_sel_buf(self.write_op_sel_fifo),
            self.write_size_buf(local_size),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_count']))
        rlast = self.m.TmpReg(prefix='rlast', initval=0)
        data_fsm(
            count(0),
            rlast(0),
        )
        data_fsm.If(cond).goto_next()

        # Data state 1
        cur_rvalid = self.m.TmpWire(prefix='cur_rvalid')
        rready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid), count > 0)
        deq_cond = vtypes.Ands(data_fsm.here, vtypes.Not(fifo.empty),
                               self.write_op_sel_buf == op_id,
                               self.write_size_buf > 0,
                               rready)

        rdata, rvalid, _ = fifo.deq_rtl(cond=deq_cond)

        wready = vtypes.Ors(self.tdata.tready, vtypes.Not(self.tdata.tvalid),
                            count > 0)

        repeat_rvalid = self.m.TmpReg(prefix='repeat_rvalid', initval=0)
        self.seq(repeat_rvalid(0))
        self.seq.If(rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        self.seq.If(repeat_rvalid, vtypes.Not(wready))(repeat_rvalid(1))
        cur_rvalid.assign(vtypes.Ors(rvalid, repeat_rvalid))

        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id,
                            count == pack_size - 1, cur_rvalid, rready)
        wdata = self.m.TmpReg(self.datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_wdata']))
        _wdata = vtypes.Cat(rdata, wdata[fifo_datawidth:self.datawidth])
        _wlast = rlast
        _ = self.write_data(_wdata, _wlast, cond=wcond)

        data_fsm.If(deq_cond)(
            rlast(self.write_size_buf <= 1)
        )

        self.seq.If(data_fsm.here, deq_cond)(
            self.write_size_buf.dec()
        )
        data_fsm.If(cur_rvalid, rready)(
            wdata(_wdata),
            count.inc(),
        )
        data_fsm.If(cur_rvalid, rready, count == pack_size - 1)(
            count(0)
        )
        data_fsm.If(count == pack_size - 1, cur_rvalid, rready, rlast).goto_init()

        self.seq.If(data_fsm.here, count == pack_size - 1, cur_rvalid, rready, rlast)(
            self.write_data_busy(0)
        )

    def _get_write_op_id(self, fifo):

        fifo_id = fifo._id()
        op = fifo_id

        if op in self.write_op_id_map:
            op_id = self.write_op_id_map[op]
        else:
            op_id = self.write_op_id_count
            self.write_op_id_count += 1
            self.write_op_id_map[op] = op_id

        return op_id

    def pack_write_req(self, op_sel, local_size):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_write_req_op_sel')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_write_req_local_size')
        _op_sel.assign(op_sel)
        _local_size.assign(local_size)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth + 1,
                                prefix='pack_write_req_packed')
        packed.assign(vtypes.Cat(_op_sel, _local_size))
        return packed

    def unpack_write_req(self, v):
        op_sel = v[self.addrwidth + 1:self.addrwidth + 1 + self.op_sel_width]
        local_size = v[0:self.addrwidth + 1]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_write_req_op_sel')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_write_req_local_size')
        _op_sel.assign(op_sel)
        _local_size.assign(local_size)
        return _op_sel, _local_size
