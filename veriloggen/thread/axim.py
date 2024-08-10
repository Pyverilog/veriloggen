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


class AXIM(axi.AxiMaster, _MutexFunction):
    """ AXI Master Interface with DMA controller """

    __intrinsics__ = {'read': 'read',
                      'write': 'write',
                      'write_fence': 'write_fence',
                      'dma_read': 'dma_read',
                      'dma_read_async': 'dma_read_async',
                      'dma_write': 'dma_write',
                      'dma_write_async': 'dma_write_async',
                      'dma_read_bank': 'dma_read_bank',
                      'dma_read_bank_async': 'dma_read_bank_async',
                      'dma_write_bank': 'dma_write_bank',
                      'dma_write_bank_async': 'dma_write_bank_async',
                      'dma_read_block': 'dma_read_block',
                      'dma_read_block_async': 'dma_read_block_async',
                      'dma_write_block': 'dma_write_block',
                      'dma_write_block_async': 'dma_write_block_async',
                      'dma_read_packed': 'dma_read_packed',
                      'dma_read_packed_async': 'dma_read_packed_async',
                      'dma_write_packed': 'dma_write_packed',
                      'dma_write_packed_async': 'dma_write_packed_async',
                      'dma_read_bcast': 'dma_read_bcast',
                      'dma_read_bcast_async': 'dma_read_bcast_async',
                      'dma_wait_read': 'dma_wait_read',
                      'dma_wait_write': 'dma_wait_write',
                      'dma_wait_write_idle': 'dma_wait_write_idle',
                      'dma_wait_write_response': 'dma_wait_write_response',
                      'dma_wait': 'dma_wait',
                      'set_global_base_addr': 'set_global_base_addr',
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 waddr_id_width=0, wdata_id_width=0, wresp_id_width=0,
                 raddr_id_width=0, rdata_id_width=0,
                 waddr_user_width=2, wdata_user_width=0, wresp_user_width=0,
                 raddr_user_width=2, rdata_user_width=0,
                 waddr_burst_mode=axi.BURST_INCR, raddr_burst_mode=axi.BURST_INCR,
                 waddr_cache_mode=axi.AxCACHE_NONCOHERENT, raddr_cache_mode=axi.AxCACHE_NONCOHERENT,
                 waddr_prot_mode=axi.AxPROT_NONCOHERENT, raddr_prot_mode=axi.AxPROT_NONCOHERENT,
                 waddr_user_mode=axi.AxUSER_NONCOHERENT, wdata_user_mode=axi.xUSER_DEFAULT,
                 raddr_user_mode=axi.AxUSER_NONCOHERENT,
                 noio=False, sb_depth=1,
                 use_global_base_addr=False,
                 op_sel_width=8, req_fifo_addrwidth=3,
                 fsm_as_module=False):

        outstanding_wcount_width = req_fifo_addrwidth
        axi.AxiMaster.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                               waddr_id_width, wdata_id_width, wresp_id_width,
                               raddr_id_width, rdata_id_width,
                               waddr_user_width, wdata_user_width, wresp_user_width,
                               raddr_user_width, rdata_user_width,
                               waddr_burst_mode, raddr_burst_mode,
                               waddr_cache_mode, raddr_cache_mode,
                               waddr_prot_mode, raddr_prot_mode,
                               waddr_user_mode, wdata_user_mode,
                               raddr_user_mode,
                               noio, outstanding_wcount_width, sb_depth)

        self.use_global_base_addr = use_global_base_addr
        self.op_sel_width = op_sel_width
        self.req_fifo_addrwidth = req_fifo_addrwidth
        self.fsm_as_module = fsm_as_module

        self.mutex = None

        # Read
        self.read_start = self.m.Reg('_'.join(['', self.name, 'read_start']),
                                     initval=0)
        self.read_op_sel = self.m.Reg('_'.join(['', self.name, 'read_op_sel']),
                                      self.op_sel_width, initval=0)
        self.read_global_addr = self.m.Reg('_'.join(['', self.name, 'read_global_addr']),
                                           self.addrwidth, initval=0)
        self.read_global_size = self.m.Reg('_'.join(['', self.name, 'read_global_size']),
                                           self.addrwidth + 1, initval=0)
        self.read_local_addr = self.m.Reg('_'.join(['', self.name, 'read_local_addr']),
                                          self.addrwidth, initval=0)
        self.read_local_stride = self.m.Reg('_'.join(['', self.name, 'read_local_stride']),
                                            self.addrwidth, initval=0)
        self.read_local_size = self.m.Reg('_'.join(['', self.name, 'read_local_size']),
                                          self.addrwidth + 1, initval=0)
        self.read_local_blocksize = self.m.Reg('_'.join(['', self.name, 'read_local_blocksize']),
                                               self.addrwidth, initval=0)

        self.read_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'read_req_fifo']),
                                  self.clk, self.rst,
                                  datawidth=self.op_sel_width + self.addrwidth * 4 + 1,
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
        self.read_local_blocksize_fifo = self.m.Wire('_'.join(['', self.name,
                                                               'read_local_blocksize_fifo']),
                                                     self.addrwidth)

        read_unpack_values = self.unpack_read_req(self.read_req_fifo.rdata)
        self.read_op_sel_fifo.assign(read_unpack_values[0])
        self.read_local_addr_fifo.assign(read_unpack_values[1])
        self.read_local_stride_fifo.assign(read_unpack_values[2])
        self.read_local_size_fifo.assign(read_unpack_values[3])
        self.read_local_blocksize_fifo.assign(read_unpack_values[4])

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
        self.read_local_blocksize_buf = self.m.Reg('_'.join(['', self.name,
                                                             'read_local_blocksize_buf']),
                                                   self.addrwidth, initval=0)

        self.read_req_busy = self.m.Reg(
            '_'.join(['', self.name, 'read_req_busy']), initval=0)
        self.read_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'read_data_busy']), initval=0)

        self.read_req_idle = self.m.Wire('_'.join(['', self.name, 'read_req_idle']))
        self.read_data_idle = self.m.Wire('_'.join(['', self.name, 'read_data_idle']))
        self.read_idle = self.m.Wire('_'.join(['', self.name, 'read_idle']))

        self.read_req_idle.assign(vtypes.Ands(vtypes.Not(self.read_start),
                                              vtypes.Not(self.read_req_busy)))
        self.read_data_idle.assign(vtypes.Ands(self.read_req_fifo.empty,
                                               vtypes.Not(self.read_data_busy)))
        self.read_idle.assign(vtypes.Ands(self.read_req_idle, self.read_data_idle))

        self.seq(
            self.read_start(0)
        )

        self.read_op_id_map = OrderedDict()
        self.read_op_id_count = 1
        self.read_ops = []

        self.read_req_fsm = None
        self.read_data_fsm = None
        self.read_data_narrow_fsm = None
        self.read_data_wide_fsm = None

        # Write
        self.write_start = self.m.Reg('_'.join(['', self.name, 'write_start']),
                                      initval=0)
        self.write_op_sel = self.m.Reg('_'.join(['', self.name, 'write_op_sel']),
                                       self.op_sel_width, initval=0)
        self.write_global_addr = self.m.Reg('_'.join(['', self.name, 'write_global_addr']),
                                            self.addrwidth, initval=0)
        self.write_global_size = self.m.Reg('_'.join(['', self.name, 'write_global_size']),
                                            self.addrwidth + 1, initval=0)
        self.write_local_addr = self.m.Reg('_'.join(['', self.name, 'write_local_addr']),
                                           self.addrwidth, initval=0)
        self.write_local_stride = self.m.Reg('_'.join(['', self.name, 'write_local_stride']),
                                             self.addrwidth, initval=0)
        self.write_local_size = self.m.Reg('_'.join(['', self.name, 'write_local_size']),
                                           self.addrwidth + 1, initval=0)
        self.write_local_blocksize = self.m.Reg('_'.join(['', self.name, 'write_local_blocksize']),
                                                self.addrwidth, initval=0)

        self.write_req_fifo = FIFO(self.m, '_'.join(['', self.name, 'write_req_fifo']),
                                   self.clk, self.rst,
                                   datawidth=self.op_sel_width + self.addrwidth * 4 + 1,
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
        self.write_local_blocksize_fifo = self.m.Wire('_'.join(['', self.name,
                                                                'write_local_blocksize_fifo']),
                                                      self.addrwidth)

        write_unpack_values = self.unpack_write_req(self.write_req_fifo.rdata)
        self.write_op_sel_fifo.assign(write_unpack_values[0])
        self.write_local_addr_fifo.assign(write_unpack_values[1])
        self.write_local_stride_fifo.assign(write_unpack_values[2])
        self.write_size_fifo.assign(write_unpack_values[3])
        self.write_local_blocksize_fifo.assign(write_unpack_values[4])

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
        self.write_local_blocksize_buf = self.m.Reg('_'.join(['', self.name,
                                                              'write_local_blocksize_buf']),
                                                    self.addrwidth, initval=0)

        self.write_req_busy = self.m.Reg(
            '_'.join(['', self.name, 'write_req_busy']), initval=0)
        self.write_data_busy = self.m.Reg(
            '_'.join(['', self.name, 'write_data_busy']), initval=0)

        self.write_req_idle = self.m.Wire('_'.join(['', self.name, 'write_req_idle']))
        self.write_data_idle = self.m.Wire('_'.join(['', self.name, 'write_data_idle']))
        self.write_idle = self.m.Wire('_'.join(['', self.name, 'write_idle']))

        self.write_req_idle.assign(vtypes.Ands(vtypes.Not(self.write_start),
                                               vtypes.Not(self.write_req_busy)))
        self.write_data_idle.assign(vtypes.Ands(self.write_req_fifo.empty,
                                                vtypes.Not(self.write_data_busy)))
        self.write_idle.assign(vtypes.Ands(self.write_req_idle, self.write_data_idle))

        self.seq(
            self.write_start(0)
        )

        self.write_op_id_map = OrderedDict()
        self.write_op_id_count = 1
        self.write_ops = []

        self.write_req_fsm = None
        self.write_data_fsm = None
        self.write_data_narrow_fsm = None
        self.write_data_wide_fsm = None

        if self.use_global_base_addr:
            self.global_base_addr = self.m.Reg('_'.join(['', self.name, 'global_base_addr']),
                                               self.addrwidth, initval=0)
        else:
            self.global_base_addr = None

    def read(self, fsm, global_addr):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1

        # state 0
        self.seq.If(fsm.here, self.read_idle)(
            self.read_req_busy(1),
            self.read_data_busy(1)
        )
        fsm.If(self.read_idle).goto_next()

        # state 1
        req_cond = fsm.here
        ack = self.read_request(global_addr, global_size, cond=req_cond)
        self.seq.If(fsm.here, ack)(
            self.read_req_busy(0)
        )
        fsm.If(ack).goto_next()

        # state 2
        rcond = fsm.here
        rdata = self.m.TmpReg(self.datawidth, initval=0,
                              signed=True, prefix='axim_rdata')
        _ = self.read_data(cond=rcond)
        fsm.If(self.rdata.rvalid)(
            rdata(self.rdata.rdata)
        )
        self.seq.If(fsm.here, self.rdata.rvalid)(
            self.read_data_busy(0)
        )
        fsm.If(self.rdata.rvalid).goto_next()

        return rdata

    def write(self, fsm, global_addr, value):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1

        # state 0
        self.seq.If(fsm.here, self.write_idle)(
            self.write_req_busy(1),
            self.write_data_busy(1)
        )
        fsm.If(self.write_idle).goto_next()

        # state 1
        req_cond = fsm.here
        ack = self.write_request(global_addr, global_size, cond=req_cond)
        self.seq.If(fsm.here, ack)(
            self.write_req_busy(0)
        )
        fsm.If(ack).goto_next()

        # state 2
        wcond = fsm.here
        wdata = value
        wlast = 1
        _ = self.write_data(wdata, wlast, cond=wcond)
        ack = vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid))
        self.seq.If(fsm.here, ack)(
            self.write_data_busy(0)
        )
        fsm.If(ack).goto_next()

    def write_fence(self, fsm, global_addr, value):

        self.write(fsm, global_addr, value)

        res = self.write_completed()
        fsm.If(res).goto_next()

    # DMA
    def dma_read(self, fsm, ram, local_addr, global_addr, local_size,
                 local_stride=1, port=0):

        local_blocksize = 1
        self._dma_read(fsm, ram, local_addr, global_addr, local_size,
                       local_stride, local_blocksize, port)

        self.dma_wait_read(fsm)

    def dma_read_async(self, fsm, ram, local_addr, global_addr, local_size,
                       local_stride=1, port=0):

        local_blocksize = 1
        self._dma_read(fsm, ram, local_addr, global_addr, local_size,
                       local_stride, local_blocksize, port)

    def dma_write(self, fsm, ram, local_addr, global_addr, local_size,
                  local_stride=1, port=0):

        local_blocksize = 1
        self._dma_write(fsm, ram, local_addr, global_addr, local_size,
                        local_stride, local_blocksize, port)

        self.dma_wait_write(fsm)

    def dma_write_async(self, fsm, ram, local_addr, global_addr, local_size,
                        local_stride=1, port=0):

        local_blocksize = 1
        self._dma_write(fsm, ram, local_addr, global_addr, local_size,
                        local_stride, local_blocksize, port)

    # DMA for each bank
    def dma_read_bank(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                      local_bank_stride=1, port=0):

        self._dma_read_bank(fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                            local_bank_stride, port)

        self.dma_wait_read(fsm)

    def dma_read_bank_async(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                            local_bank_stride=1, port=0):

        self._dma_read_bank(fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                            local_bank_stride, port)

    def _dma_read_bank(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                       local_bank_stride=1, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            raise TypeError("'ram' must be MultibankRAM, not '%s'" % str(type(ram)))

        check = fsm.current
        fsm.set_index(check + 1)

        starts = []
        ends = []
        for i, _ram in enumerate(ram.rams):
            starts.append(fsm.current)
            local_blocksize = 1
            self._dma_read(fsm, _ram, local_bank_addr, global_addr, local_bank_size,
                           local_bank_stride, local_blocksize, port)
            ends.append(fsm.current)
            fsm.set_index(fsm.current + 1)

        fin = fsm.current

        for i, (s, e) in enumerate(zip(starts, ends)):
            fsm.goto_from(check, s, cond=bank == i)
            fsm.goto_from(e, fin)

    def dma_write_bank(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                       local_bank_stride=1, port=0):

        self._dma_write_bank(fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride, port)

        self.dma_wait_write(fsm)

    def dma_write_bank_async(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride=1, port=0):

        self._dma_write_bank(fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride, port)

    def _dma_write_bank(self, fsm, ram, bank, local_bank_addr, global_addr, local_bank_size,
                        local_bank_stride=1, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            raise TypeError("'ram' must be MultibankRAM, not '%s'" % str(type(ram)))

        check = fsm.current
        fsm.set_index(check + 1)

        starts = []
        ends = []
        for i, _ram in enumerate(ram.rams):
            starts.append(fsm.current)
            local_blocksize = 1
            self._dma_write(fsm, _ram, local_bank_addr, global_addr, local_bank_size,
                            local_bank_stride, local_blocksize, port)
            ends.append(fsm.current)
            fsm.set_index(fsm.current + 1)

        fin = fsm.current

        for i, (s, e) in enumerate(zip(starts, ends)):
            fsm.goto_from(check, s, cond=bank == i)
            fsm.goto_from(e, fin)

    # DMA with block interleave
    def dma_read_block(self, fsm, ram, local_bank_addr, global_addr, local_size,
                       local_blocksize=1, local_stride=None, port=0):

        self._dma_read_block(fsm, ram, local_bank_addr, global_addr, local_size,
                             local_blocksize, local_stride, port)

        self.dma_wait_read(fsm)

    def dma_read_block_async(self, fsm, ram, local_bank_addr, global_addr, local_size,
                             local_blocksize=1, local_stride=None, port=0):

        self._dma_read_block(fsm, ram, local_bank_addr, global_addr, local_size,
                             local_blocksize, local_stride, port)

    def _dma_read_block(self, fsm, ram, local_bank_addr, global_addr, local_size,
                        local_blocksize=1, local_stride=None, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            raise TypeError("'ram' must be MultibankRAM, not '%s'" % str(type(ram)))

        if isinstance(ram.rams[0], MultibankRAM):
            if local_stride is None:
                local_stride = ram.rams[0].numbanks

            high_local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                             prefix='_dma_write_block_high_local_size')
            high_local_size.assign(local_size >> ram.rams[0].shift)

            low_local_size = self.m.TmpWire(ram.rams[0].shift,
                                            prefix='_dma_write_block_low_local_size')
            mask = vtypes.Repeat(vtypes.Int(1, 1), ram.rams[0].shift)
            low_local_size.assign(vtypes.And(local_size, mask))

            local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                        prefix='_dma_write_block_local_size')
            local_size.assign(vtypes.Mux(low_local_size > 0,
                                         high_local_size + 1, high_local_size))

            high_local_blocksize = self.m.TmpWire(vtypes.get_width(local_blocksize),
                                                  prefix='_dma_read_block_high_local_blocksize')
            high_local_blocksize.assign(local_blocksize >> ram.rams[0].shift)
            low_local_blocksize = self.m.TmpWire(vtypes.get_width(ram.rams[0].shift),
                                                 prefix='_dma_read_block_low_local_blocksize')
            mask = vtypes.Repeat(vtypes.Int(1, 1), ram.rams[0].shift)
            low_local_blocksize.assign(vtypes.And(local_blocksize, mask))
            local_blocksize = self.m.TmpWire(vtypes.get_width(local_blocksize),
                                             prefix='_dma_read_block_local_blocksize')
            local_blocksize.assign(vtypes.Mux(low_local_blocksize > 0,
                                              high_local_blocksize + 1, high_local_blocksize))

        elif local_stride is None:
            local_stride = 1

        ram_method = ram.write_burst_block
        self._dma_read(fsm, ram, local_bank_addr, global_addr, local_size,
                       local_stride, local_blocksize, port, ram_method)

    def dma_write_block(self, fsm, ram, local_bank_addr, global_addr, local_size,
                        local_blocksize=1, local_stride=None, port=0):

        self._dma_write_block(fsm, ram, local_bank_addr, global_addr, local_size,
                              local_blocksize, local_stride, port)

        self.dma_wait_write(fsm)

    def dma_write_block_async(self, fsm, ram, local_bank_addr, global_addr, local_size,
                              local_blocksize=1, local_stride=None, port=0):

        self._dma_write_block(fsm, ram, local_bank_addr, global_addr, local_size,
                              local_blocksize, local_stride, port)

    def _dma_write_block(self, fsm, ram, local_bank_addr, global_addr, local_size,
                         local_blocksize=1, local_stride=None, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            raise TypeError("'ram' must be MultibankRAM, not '%s'" % str(type(ram)))

        if isinstance(ram.rams[0], MultibankRAM):
            if local_stride is None:
                local_stride = ram.rams[0].numbanks

            high_local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                             prefix='_dma_read_block_high_local_size')
            high_local_size.assign(local_size >> ram.rams[0].shift)

            low_local_size = self.m.TmpWire(ram.rams[0].shift,
                                            prefix='_dma_read_block_low_local_size')
            mask = vtypes.Repeat(vtypes.Int(1, 1), ram.rams[0].shift)
            low_local_size.assign(vtypes.And(local_size, mask))

            local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                        prefix='_dma_read_block_local_size')
            local_size.assign(vtypes.Mux(low_local_size > 0,
                                         high_local_size + 1, high_local_size))

            high_local_blocksize = self.m.TmpWire(vtypes.get_width(local_blocksize),
                                                  prefix='_dma_write_block_high_local_blocksize')
            high_local_blocksize.assign(local_blocksize >> ram.rams[0].shift)
            low_local_blocksize = self.m.TmpWire(vtypes.get_width(ram.rams[0].shift),
                                                 prefix='_dma_write_block_low_local_blocksize')
            mask = vtypes.Repeat(vtypes.Int(1, 1), ram.rams[0].shift)
            low_local_blocksize.assign(vtypes.And(local_blocksize, mask))
            local_blocksize = self.m.TmpWire(vtypes.get_width(local_blocksize),
                                             prefix='_dma_write_block_local_blocksize')
            local_blocksize.assign(vtypes.Mux(low_local_blocksize > 0,
                                              high_local_blocksize + 1, high_local_blocksize))

        elif local_stride is None:
            local_stride = 1

        ram_method = ram.read_burst_block
        self._dma_write(fsm, ram, local_bank_addr, global_addr, local_size,
                        local_stride, local_blocksize, port, ram_method)

    # multi-bank packed DMA
    def dma_read_packed(self, fsm, ram, local_addr, global_addr, local_size,
                        local_stride=None, port=0):

        self._dma_read_packed(fsm, ram, local_addr, global_addr, local_size,
                              local_stride, port)

        self.dma_wait_read(fsm)

    def dma_read_packed_async(self, fsm, ram, local_addr, global_addr, local_size,
                              local_stride=None, port=0):

        self._dma_read_packed(fsm, ram, local_addr, global_addr, local_size,
                              local_stride, port)

    def _dma_read_packed(self, fsm, ram, local_addr, global_addr, local_size,
                         local_stride=None, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            local_stride = 1
            local_blocksize = 1
            return self._dma_read(fsm, ram, local_addr, global_addr, local_size,
                                  local_stride, local_blocksize, port)

        if local_stride is None:
            local_stride = ram.numbanks

        high_local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                         prefix='_dma_read_packed_high_local_size')
        high_local_size.assign(local_size >> ram.shift)

        low_local_size = self.m.TmpWire(ram.shift,
                                        prefix='_dma_read_packed_low_local_size')
        mask = vtypes.Repeat(vtypes.Int(1, 1), ram.shift)
        low_local_size.assign(vtypes.And(local_size, mask))

        local_packed_size = self.m.TmpWire(vtypes.get_width(local_size),
                                           prefix='_dma_read_packed_local_packed_size')
        local_packed_size.assign(vtypes.Mux(low_local_size > 0,
                                            high_local_size + 1, high_local_size))

        ram_method = ram.write_burst_packed
        local_blocksize = 1
        self._dma_read(fsm, ram, local_addr, global_addr, local_packed_size,
                       local_stride, local_blocksize, port, ram_method)

    def dma_write_packed(self, fsm, ram, local_addr, global_addr, local_size,
                         local_stride=None, port=0):

        self._dma_write_packed(fsm, ram, local_addr, global_addr, local_size,
                               local_stride, port)

        self.dma_wait_write(fsm)

    def dma_write_packed_async(self, fsm, ram, local_addr, global_addr, local_size,
                               local_stride=None, port=0):

        self._dma_write_packed(fsm, ram, local_addr, global_addr, local_size,
                               local_stride, port)

    def _dma_write_packed(self, fsm, ram, local_addr, global_addr, local_size,
                          local_stride=None, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            local_stride = 1
            local_blocksize = 1
            return self._dma_write(fsm, ram, local_addr, global_addr, local_size,
                                   local_stride, local_blocksize, port)

        if local_stride is None:
            local_stride = ram.numbanks

        high_local_size = self.m.TmpWire(vtypes.get_width(local_size),
                                         prefix='_dma_write_packed_high_local_size')
        high_local_size.assign(local_size >> ram.shift)

        low_local_size = self.m.TmpWire(ram.shift,
                                        prefix='_dma_write_packed_low_local_size')
        mask = vtypes.Repeat(vtypes.Int(1, 1), ram.shift)
        low_local_size.assign(vtypes.And(local_size, mask))

        local_packed_size = self.m.TmpWire(vtypes.get_width(local_size),
                                           prefix='_dma_write_packed_local_packed_size')
        local_packed_size.assign(vtypes.Mux(low_local_size > 0,
                                            high_local_size + 1, high_local_size))

        ram_method = ram.read_burst_packed
        local_blocksize = 1
        self._dma_write(fsm, ram, local_addr, global_addr, local_packed_size,
                        local_stride, local_blocksize, port, ram_method)

    # DMA with broadcast
    def dma_read_bcast(self, fsm, ram, local_bank_addr, global_addr, local_bank_size,
                       local_bank_stride=1, port=0):

        self._dma_read_bcast(fsm, ram, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride, port)

        self.dma_wait_read(fsm)

    def dma_read_bcast_async(self, fsm, ram, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride=1, port=0):

        self._dma_read_bcast(fsm, ram, local_bank_addr, global_addr, local_bank_size,
                             local_bank_stride, port)

    def _dma_read_bcast(self, fsm, ram, local_bank_addr, global_addr, local_bank_size,
                        local_bank_stride=1, port=0):

        if isinstance(ram, (tuple, list)):
            ram = to_multibank_ram(ram)

        if not isinstance(ram, MultibankRAM):
            raise TypeError("'ram' must be MultibankRAM, not '%s'" % str(type(ram)))

        ram_method = ram.write_burst_bcast
        local_blocksize = 1
        self._dma_read(fsm, ram, local_bank_addr, global_addr, local_bank_size,
                       local_bank_stride, local_blocksize, port, ram_method)

    # wait
    def dma_wait_read(self, fsm):

        fsm.If(self.read_idle).goto_next()

    def dma_wait_write(self, fsm):

        res = self.write_completed()
        fsm.If(self.write_idle, res).goto_next()

    def dma_wait_write_idle(self, fsm):

        fsm.If(self.write_idle).goto_next()

    def dma_wait_write_response(self, fsm):

        res = self.write_completed()
        fsm.If(res).goto_next()

    def dma_wait(self, fsm):

        res = self.write_completed()
        fsm.If(self.read_idle, self.write_idle, res).goto_next()

    def set_global_base_addr(self, fsm, addr):

        if not self.use_global_base_addr:
            raise ValueError("global_base_addr is disabled.")

        flag = self._set_flag(fsm)
        self.seq.If(flag)(
            self.global_base_addr(addr)
        )
        fsm.goto_next()

    # --------------------
    # read
    # --------------------
    def _dma_read(self, fsm, ram, local_addr, global_addr, local_size,
                  local_stride=1, local_blocksize=1, port=0, ram_method=None):

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

        global_size = local_size

        start = vtypes.Ands(fsm.here, self.read_req_idle)

        self._set_read_request(ram, port, ram_method, ram_datawidth,
                               start, local_addr, global_addr,
                               local_size, global_size, local_stride, local_blocksize)
        self._synthesize_read_req_fsm()
        self._synthesize_read_data_fsm(ram, port, ram_method, ram_datawidth)

        fsm.If(self.read_req_idle).goto_next()

    def _set_read_request(self, ram, port, ram_method, ram_datawidth,
                          start, local_addr, global_addr,
                          local_size, global_size, local_stride, local_blocksize):

        # adjust global_size
        if self.datawidth == ram_datawidth:
            # same
            pass

        elif self.datawidth < ram_datawidth:
            # narrow
            pack_size = ram_datawidth // self.datawidth
            global_size = (global_size << int(math.log(pack_size, 2))
                           if pack_size & (pack_size - 1) == 0 else
                           global_size * pack_size)

        elif self.datawidth > ram_datawidth:
            # wide
            pack_size = self.datawidth // ram_datawidth
            shamt = int(math.log(pack_size, 2))
            res = vtypes.Mux(
                vtypes.And(global_size, 2 ** shamt - 1) > 0, 1, 0)
            global_size = vtypes.Add((global_size >> shamt), res)

        op_id = self._get_read_op_id(ram, port, ram_method)

        if self.use_global_base_addr:
            global_addr = global_addr + self.global_base_addr

        self.seq.If(start)(
            self.read_start(1),
            self.read_op_sel(op_id),
            self.read_global_addr(self.mask_addr(global_addr)),
            self.read_global_size(global_size),
            self.read_local_addr(local_addr),
            self.read_local_stride(local_stride),
            self.read_local_size(local_size),
            self.read_local_blocksize(local_blocksize),
        )

    def _synthesize_read_req_fsm(self):

        if self.read_req_fsm is not None:
            return

        req_fsm = FSM(self.m, '_'.join(['', self.name, 'read_req_fsm']),
                      self.clk, self.rst, as_module=self.fsm_as_module)
        self.read_req_fsm = req_fsm

        cur_global_size = self.m.Reg('_'.join(['', self.name, 'read_cur_global_size']),
                                     self.addrwidth + 1, initval=0)
        cont = self.m.Reg('_'.join(['', self.name, 'read_cont']), initval=0)
        max_burstlen = 2 ** self.burst_size_width

        # Req state 0
        self.seq.If(req_fsm.here, self.read_start)(
            self.read_req_busy(1)
        )
        self.seq.If(self.read_start, self.read_req_fifo.almost_full)(
            self.read_start(1)
        )

        enq_cond = vtypes.Ands(req_fsm.here, self.read_start,
                               vtypes.Not(self.read_req_fifo.almost_full))
        _ = self.read_req_fifo.enq_rtl(self.pack_read_req(self.read_op_sel,
                                                          self.read_local_addr,
                                                          self.read_local_stride,
                                                          self.read_local_size,
                                                          self.read_local_blocksize),
                                       cond=enq_cond)

        check_cond = vtypes.Ands(req_fsm.here, vtypes.Ors(self.read_start, cont),
                                 vtypes.Not(self.read_req_fifo.almost_full))
        self._check_4KB_boundary(req_fsm, max_burstlen,
                                 self.read_global_addr, cur_global_size, self.read_global_size,
                                 cond=check_cond)
        req_fsm.If(check_cond).goto_next()

        # Req state 1
        ack = self.read_request(self.read_global_addr, cur_global_size, cond=req_fsm)
        req_fsm.If(ack)(
            cont(1)
        )
        self.seq.If(req_fsm.here, ack)(
            self.read_global_addr.add(optimize(cur_global_size * (self.datawidth // 8)))
        )
        req_fsm.If(ack, self.read_global_size == 0)(
            cont(0)
        )
        self.seq.If(req_fsm.here, ack, self.read_global_size == 0)(
            self.read_req_busy(0)
        )
        req_fsm.If(ack).goto_init()

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
            self.read_local_blocksize_buf(self.read_local_blocksize_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.read_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        ram_cond = vtypes.Ands(data_fsm.here, self.read_op_sel_buf == op_id)
        ram_method(self.read_local_addr_buf, self.read_local_stride_buf,
                   self.read_local_size_buf, self.read_local_blocksize_buf,
                   self.rdata.rdata, self.rdata.rvalid, False,
                   port=port, cond=ram_cond)
        data_fsm.goto_next()

        # Data state 2
        _ = self.read_data(cond=data_fsm)
        self.seq.If(data_fsm.here, self.rdata.rvalid)(
            self.read_local_size_buf.dec()
        )

        data_fsm.If(self.rdata.rvalid, self.read_local_size_buf <= 1).goto_init()
        self.seq.If(data_fsm.here, self.rdata.rvalid, self.read_local_size_buf <= 1)(
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
            self.read_local_blocksize_buf(self.read_local_blocksize_fifo),
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
                   self.read_local_size_buf, self.read_local_blocksize_buf,
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
        data_fsm.If(cond, self.rdata.rvalid, count < pack_size - 1)(
            count.inc(),
            wdata(vtypes.Cat(self.rdata.rdata, wdata[self.datawidth:])),
            wvalid(0),
        )
        data_fsm.If(cond, self.rdata.rvalid, count == pack_size - 1)(
            count(0),
            wdata(vtypes.Cat(self.rdata.rdata, wdata[self.datawidth:])),
            wvalid(1)
        )
        self.seq.If(data_fsm.here, cond, self.rdata.rvalid, count == pack_size - 1)(
            self.read_local_size_buf.dec()
        )

        data_fsm.If(cond, self.rdata.rvalid, self.read_local_size_buf <= 1,
                    count == pack_size - 1).goto_init()
        self.seq.If(data_fsm.here, cond, self.rdata.rvalid, self.read_local_size_buf <= 1,
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
            self.read_local_blocksize_buf(self.read_local_blocksize_fifo),
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
                   self.read_local_size_buf, self.read_local_blocksize_buf,
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
        data_fsm.If(cond, self.rdata.rvalid, count == 0)(
            count.inc(),
            wdata(self.rdata.rdata),
            wvalid(1),
        )
        self.seq.If(data_fsm.here, cond, self.rdata.rvalid, count == 0)(
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
                    cond, self.rdata.rvalid, count == 0).goto_init()
        self.seq.If(data_fsm.here, self.read_local_size_buf <= 1,
                    cond, count > 0)(
            self.read_data_busy(0)
        )
        self.seq.If(data_fsm.here, self.read_local_size_buf <= 1,
                    cond, self.rdata.rvalid, count == 0)(
            self.read_data_busy(0)
        )

    # --------------------
    # write
    # --------------------
    def _dma_write(self, fsm, ram, local_addr, global_addr, local_size,
                   local_stride=1, local_blocksize=1, port=0, ram_method=None):

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

        global_size = local_size

        start = vtypes.Ands(fsm.here, self.write_req_idle)

        self._set_write_request(ram, port, ram_method, ram_datawidth,
                                start, local_addr, global_addr,
                                local_size, global_size, local_stride, local_blocksize)
        self._synthesize_write_req_fsm()
        self._synthesize_write_data_fsm(ram, port, ram_method, ram_datawidth)

        fsm.If(self.write_req_idle).goto_next()

    def _set_write_request(self, ram, port, ram_method, ram_datawidth,
                           start, local_addr, global_addr,
                           local_size, global_size, local_stride, local_blocksize):

        # adjust global_size
        if self.datawidth == ram_datawidth:
            # same
            pass

        elif self.datawidth < ram_datawidth:
            # narrow
            pack_size = ram_datawidth // self.datawidth
            global_size = (global_size << int(math.log(pack_size, 2))
                           if pack_size & (pack_size - 1) == 0 else
                           global_size * pack_size)

        elif self.datawidth > ram_datawidth:
            # wide
            pack_size = self.datawidth // ram_datawidth
            shamt = int(math.log(pack_size, 2))
            res = vtypes.Mux(
                vtypes.And(global_size, 2 ** shamt - 1) > 0, 1, 0)
            global_size = vtypes.Add((global_size >> shamt), res)

        op_id = self._get_write_op_id(ram, port, ram_method)

        if self.use_global_base_addr:
            global_addr = global_addr + self.global_base_addr

        self.seq.If(start)(
            self.write_start(1),
            self.write_op_sel(op_id),
            self.write_global_addr(self.mask_addr(global_addr)),
            self.write_global_size(global_size),
            self.write_local_addr(local_addr),
            self.write_local_stride(local_stride),
            self.write_local_size(local_size),
            self.write_local_blocksize(local_blocksize),
        )

    def _synthesize_write_req_fsm(self):

        if self.write_req_fsm is not None:
            return

        req_fsm = FSM(self.m, '_'.join(['', self.name, 'write_req_fsm']),
                      self.clk, self.rst, as_module=self.fsm_as_module)
        self.write_req_fsm = req_fsm

        cur_global_size = self.m.Reg('_'.join(['', self.name, 'write_cur_global_size']),
                                     self.addrwidth + 1, initval=0)
        cont = self.m.Reg('_'.join(['', self.name, 'write_cont']), initval=0)
        max_burstlen = 2 ** self.burst_size_width

        # Req state 0
        self.seq.If(req_fsm.here, self.write_start)(
            self.write_req_busy(1)
        )
        self.seq.If(self.write_start, self.write_req_fifo.almost_full)(
            self.write_start(1)
        )

        enq_cond = vtypes.Ands(req_fsm.here, self.write_start,
                               vtypes.Not(self.write_req_fifo.almost_full))
        _ = self.write_req_fifo.enq_rtl(self.pack_write_req(self.write_op_sel,
                                                            self.write_local_addr,
                                                            self.write_local_stride,
                                                            self.write_local_size,
                                                            self.write_local_blocksize),
                                        cond=enq_cond)

        check_cond = vtypes.Ands(req_fsm.here, vtypes.Ors(self.write_start, cont),
                                 vtypes.Not(self.write_req_fifo.almost_full))
        self._check_4KB_boundary(req_fsm, max_burstlen,
                                 self.write_global_addr, cur_global_size, self.write_global_size,
                                 cond=check_cond)
        req_fsm.If(check_cond).goto_next()

        # Req state 1
        enq_cond = vtypes.Ands(req_fsm.here,
                               vtypes.Not(self.write_req_fifo.almost_full),
                               vtypes.Ors(self.waddr.awready, vtypes.Not(self.waddr.awvalid)),
                               self.write_acceptable())
        _ = self.write_req_fifo.enq_rtl(self.pack_write_req(self.write_op_sel,
                                                            self.write_local_addr,
                                                            self.write_local_stride,
                                                            # converted into local_size after deque
                                                            cur_global_size,
                                                            self.write_local_blocksize),
                                        cond=enq_cond)

        req_cond = vtypes.Ands(req_fsm.here,
                               vtypes.Not(self.write_req_fifo.almost_full),
                               self.write_acceptable())
        ack = self.write_request(self.write_global_addr, cur_global_size, cond=req_cond)
        req_fsm.If(enq_cond)(
            cont(1)
        )
        self.seq.If(req_fsm.here, enq_cond)(
            self.write_global_addr.add(optimize(cur_global_size * (self.datawidth // 8)))
        )
        req_fsm.If(enq_cond, self.write_global_size == 0)(
            cont(0)
        )
        self.seq.If(req_fsm.here, enq_cond, self.write_global_size == 0)(
            self.write_req_busy(0)
        )
        req_fsm.If(enq_cond).goto_init()

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
            data_fsm.set_index(0)

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
            self.write_local_blocksize_buf(self.write_local_blocksize_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        self.seq.If(data_fsm.here)(
            self.write_size_buf(0)
        )

        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        rready = vtypes.Ands(vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid)),
                             self.write_size_buf > 0)
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, self.write_local_blocksize_buf,
            rready, port=port, cond=ram_cond)
        data_fsm.goto_next()

        # Data state 2
        cond = vtypes.Ands(vtypes.Not(self.write_req_fifo.empty),
                           self.write_size_buf == 0)
        self.seq.If(data_fsm.here, cond)(
            self.write_size_buf(self.write_size_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        wcond = vtypes.Ands(self.write_op_sel_buf == op_id, rvalid, rready)
        _rlast = vtypes.Ors(rlast, self.write_size_buf == 1)
        _ = self.write_data(rdata, _rlast, cond=wcond)
        self.seq.If(data_fsm.here, rvalid, rready)(
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

        self.write_ops.append(op_id)

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
            self.write_local_blocksize_buf(self.write_local_blocksize_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        self.seq.If(data_fsm.here)(
            self.write_size_buf(0)
        )

        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_count']))
        rready = vtypes.Ands(vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid)),
                             count == 0, self.write_size_buf > 0)
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, self.write_local_blocksize_buf,
            rready, port=port, cond=ram_cond)

        data_fsm(
            count(0)
        )
        data_fsm.goto_next()

        # Data state 2
        deq_cond = vtypes.Ands(data_fsm.here,
                               vtypes.Not(self.write_req_fifo.empty),
                               self.write_size_buf == 0)

        self.seq.If(data_fsm.here, deq_cond)(
            # write_size_fifo: global_size
            self.write_size_buf(self.write_size_fifo),
        )
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        wdata = self.m.TmpReg(ram_datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wdata']))
        wlast = self.m.TmpReg(initval=0,
                              prefix='_'.join(['', self.name, 'write_narrow_wlast']))
        wack = vtypes.Ands(vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid)),
                           self.write_size_buf > 0)
        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id, wack,
                            vtypes.Ors(count > 0, rvalid))
        _wdata = vtypes.Mux(count == 0, rdata[:self.datawidth], wdata[:self.datawidth])
        _wlast = self.write_size_buf == 1
        self.write_data(_wdata, _wlast, cond=wcond)

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
            self.write_local_blocksize_buf(self.write_local_blocksize_fifo),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)
        data_fsm.If(cond).goto_next()

        # Data state 1
        self.seq.If(data_fsm.here)(
            self.write_size_buf(0)
        )

        ram_cond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id)
        count = self.m.TmpReg(log_pack_size, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_count']))
        rready = vtypes.Ands(vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid), count > 0),
                             self.write_size_buf > 0)
        rdata, rvalid, rlast = ram_method(
            self.write_local_addr_buf, self.write_local_stride_buf,
            self.write_size_buf, self.write_local_blocksize_buf,
            rready, port=port, cond=ram_cond)

        data_fsm(
            count(0)
        )
        data_fsm.goto_next()

        # Data state 2
        cond = vtypes.Ands(vtypes.Not(self.write_req_fifo.empty),
                           self.write_size_buf == 0)
        self.seq.If(data_fsm.here, cond)(
            # global_size -> local_size
            self.write_size_buf(self.write_size_fifo << log_pack_size),
        )
        deq_cond = vtypes.Ands(data_fsm.here, cond)
        _ = self.write_req_fifo.deq_rtl(cond=deq_cond)

        wcond = vtypes.Ands(data_fsm.here, self.write_op_sel_buf == op_id,
                            count == pack_size - 1, rvalid, rready)
        wdata = self.m.TmpReg(self.datawidth, initval=0,
                              prefix='_'.join(['', self.name, 'write_wide_wdata']))
        _wdata = vtypes.Cat(rdata, wdata[ram_datawidth:self.datawidth])
        _wlast = vtypes.Ors(rlast, self.write_size_buf == 1)
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

    def _set_flag(self, fsm, prefix='axim_flag'):
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

    def _check_4KB_boundary(self, fsm, max_burstlen,
                            req_global_addr, req_size, rest_size, cond=None):

        self.seq.If(cond, rest_size <= max_burstlen,
                    self.check_boundary(req_global_addr, rest_size))(
            req_size(self.rest_boundary(req_global_addr)),
            rest_size(
                rest_size - self.rest_boundary(req_global_addr))
        ).Elif(cond, rest_size <= max_burstlen)(
            req_size(rest_size),
            rest_size(0)
        ).Elif(cond, self.check_boundary(req_global_addr, max_burstlen))(
            req_size(self.rest_boundary(req_global_addr)),
            rest_size(
                rest_size - self.rest_boundary(req_global_addr))
        ).Elif(cond)(
            req_size(max_burstlen),
            rest_size(rest_size - max_burstlen)
        )

    def pack_read_req(self, op_sel, local_addr, local_stride, local_size, local_blocksize):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_read_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='pack_read_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='pack_read_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_read_req_local_size')
        _local_blocksize = self.m.TmpWire(self.addrwidth, prefix='pack_read_req_local_blocksize')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        _local_blocksize.assign(local_blocksize)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth * 4 + 1,
                                prefix='pack_read_req_packed')
        packed.assign(
            vtypes.Cat(_op_sel, _local_addr, _local_stride, _local_size, _local_blocksize))
        return packed

    def unpack_read_req(self, v):
        op_sel = v[self.addrwidth * 4 + 1:self.addrwidth * 4 + 1 + self.op_sel_width]
        local_addr = v[self.addrwidth * 3 + 1:self.addrwidth * 3 + 1 + self.addrwidth]
        local_stride = v[self.addrwidth * 2 + 1:self.addrwidth * 2 + 1 + self.addrwidth]
        local_size = v[self.addrwidth:self.addrwidth * 2 + 1]
        local_blocksize = v[0:self.addrwidth]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_read_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='unpack_read_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='unpack_read_req_local_stride')
        _local_size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_read_req_local_size')
        _local_blocksize = self.m.TmpWire(self.addrwidth, prefix='unpack_read_req_local_blocksize')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _local_size.assign(local_size)
        _local_blocksize.assign(local_blocksize)
        return _op_sel, _local_addr, _local_stride, _local_size, _local_blocksize

    def pack_write_req(self, op_sel, local_addr, local_stride, size, local_blocksize):
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='pack_write_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='pack_write_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='pack_write_req_local_stride')
        _size = self.m.TmpWire(self.addrwidth + 1, prefix='pack_write_req_size')
        _local_blocksize = self.m.TmpWire(self.addrwidth, prefix='pack_write_req_local_blocksize')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _size.assign(size)
        _local_blocksize.assign(local_blocksize)
        packed = self.m.TmpWire(self.op_sel_width + self.addrwidth * 4 + 1,
                                prefix='pack_write_req_packed')
        packed.assign(
            vtypes.Cat(_op_sel, _local_addr, _local_stride, _size, _local_blocksize))
        return packed

    def unpack_write_req(self, v):
        op_sel = v[self.addrwidth * 4 + 1:self.addrwidth * 4 + 1 + self.op_sel_width]
        local_addr = v[self.addrwidth * 3 + 1:self.addrwidth * 3 + 1 + self.addrwidth]
        local_stride = v[self.addrwidth * 2 + 1:self.addrwidth * 2 + 1 + self.addrwidth]
        size = v[self.addrwidth:self.addrwidth * 2 + 1]
        local_blocksize = v[0:self.addrwidth]
        _op_sel = self.m.TmpWire(self.op_sel_width, prefix='unpack_write_req_op_sel')
        _local_addr = self.m.TmpWire(self.addrwidth, prefix='unpack_write_req_local_addr')
        _local_stride = self.m.TmpWire(self.addrwidth, prefix='unpack_write_req_local_stride')
        _size = self.m.TmpWire(self.addrwidth + 1, prefix='unpack_write_req_size')
        _local_blocksize = self.m.TmpWire(self.addrwidth, prefix='unpack_write_req_local_blocksize')
        _op_sel.assign(op_sel)
        _local_addr.assign(local_addr)
        _local_stride.assign(local_stride)
        _size.assign(size)
        _local_blocksize.assign(local_blocksize)
        return _op_sel, _local_addr, _local_stride, _size, _local_blocksize


class AXIMVerify(AXIM):
    __intrinsics__ = {'read_delayed': 'read_delayed',
                      'write_delayed': 'write_delayed'} | AXIM.__intrinsics__

    def read_delayed(self, fsm, global_addr, delay):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1
        delay_count = self.m.TmpReg(self.addrwidth, initval=0, prefix='delay_count')

        # state 0
        self.seq.If(fsm.here, self.read_idle)(
            self.read_req_busy(1),
            self.read_data_busy(1)
        )
        fsm(
            delay_count(delay)
        )
        fsm.If(self.read_idle).goto_next()

        # state 1
        req_cond = fsm.here
        ack = self.read_request(global_addr, global_size, cond=req_cond)
        self.seq.If(fsm.here, ack)(
            self.read_req_busy(0)
        )
        fsm.If(ack).goto_next()

        # state 2
        fsm.If(delay_count > 0)(
            delay_count.dec()
        )
        fsm.If(delay_count == 0).goto_next()

        # state 3
        rcond = fsm.here
        rdata = self.m.TmpReg(self.datawidth, initval=0,
                              signed=True, prefix='axim_rdata')
        _ = self.read_data(cond=rcond)
        fsm.If(self.rdata.rvalid)(
            rdata(self.rdata.rdata)
        )
        self.seq.If(fsm.here, self.rdata.rvalid)(
            self.read_data_busy(0)
        )
        fsm.If(self.rdata.rvalid).goto_next()

        return rdata

    def write_delayed(self, fsm, global_addr, value, delay):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1
        delay_count = self.m.TmpReg(self.addrwidth, initval=0, prefix='delay_count')

        # state 0
        self.seq.If(fsm.here, self.write_idle)(
            self.write_req_busy(1),
            self.write_data_busy(1)
        )
        fsm(
            delay_count(delay)
        )
        fsm.If(self.write_idle).goto_next()

        # state 1
        req_cond = fsm.here
        ack = self.write_request(global_addr, global_size, cond=req_cond)
        self.seq.If(fsm.here, ack)(
            self.write_req_busy(0)
        )
        fsm.If(ack).goto_next()

        # state 2
        fsm.If(delay_count > 0)(
            delay_count.dec()
        )
        fsm.If(delay_count == 0).goto_next()

        # state 3
        wcond = fsm.here
        wdata = value
        wlast = 1
        _ = self.write_data(wdata, wlast, cond=wcond)
        ack = vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid))
        self.seq.If(fsm.here, ack)(
            self.write_data_busy(0)
        )
        fsm.If(ack).goto_next()


class AXIMLite(axi.AxiLiteMaster, _MutexFunction):
    """ AXI-Lite Master Interface """

    __intrinsics__ = {'read': 'read',
                      'write': 'write',
                      'write_fence': 'write_fence',
                      'set_global_base_addr': 'set_global_base_addr'
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 waddr_cache_mode=axi.AxCACHE_NONCOHERENT, raddr_cache_mode=axi.AxCACHE_NONCOHERENT,
                 waddr_prot_mode=axi.AxPROT_NONCOHERENT, raddr_prot_mode=axi.AxPROT_NONCOHERENT,
                 noio=False, sb_depth=1,
                 use_global_base_addr=False,
                 fsm_as_module=False):

        outstanding_wcount_width = 3
        axi.AxiLiteMaster.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                                   waddr_cache_mode, raddr_cache_mode,
                                   waddr_prot_mode, raddr_prot_mode,
                                   noio, outstanding_wcount_width, sb_depth)

        self.use_global_base_addr = use_global_base_addr
        self.fsm_as_module = fsm_as_module

        self.mutex = None

    def read(self, fsm, global_addr):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1

        # state 0
        req_cond = fsm.here
        ack = self.read_request(global_addr, global_size, cond=req_cond)
        fsm.If(ack).goto_next()

        # state 1
        done = vtypes.Ands(self.raddr.arvalid, self.raddr.arready)
        fsm.If(done).goto_next()

        # state 2
        rcond = fsm.here
        rdata = self.m.TmpReg(self.datawidth, initval=0,
                              signed=True, prefix='axim_rdata')
        _ = self.read_data(cond=rcond)
        fsm.If(self.rdata.rvalid)(
            rdata(self.rdata.rdata)
        )
        fsm.If(self.rdata.rvalid).goto_next()

        return rdata

    def write(self, fsm, global_addr, value):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1

        # state 0
        req_cond = fsm.here
        ack = self.write_request(global_addr, global_size, cond=req_cond)
        fsm.If(ack).goto_next()

        # state 1
        done = vtypes.Ands(self.waddr.awvalid, self.waddr.awready)
        fsm.If(done).goto_next()

        # state 2
        wcond = fsm.here
        wdata = value
        _ = self.write_data(wdata, cond=wcond)
        ack = vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid))
        fsm.If(ack).goto_next()

        # state 3
        done = vtypes.Ands(self.wdata.wvalid, self.wdata.wready)
        fsm.If(done).goto_next()

        # state 4
        res = self.write_completed()
        fsm.If(res).goto_next()

    def write_fence(self, fsm, global_addr, value):
        """ AXI-Lite Master must not issue any request until the previous request is completed."""
        self.write(fsm, global_addr, value)

    def set_global_base_addr(self, fsm, addr):

        if not self.use_global_base_addr:
            raise ValueError("global_base_addr is disabled.")

        flag = self._set_flag(fsm)
        self.seq.If(flag)(
            self.global_base_addr(addr)
        )


class AXIMLiteVerify(AXIMLite):
    __intrinsics__ = {'read_delayed': 'read_delayed',
                      'write_delayed': 'write_delayed'} | AXIMLite.__intrinsics__

    def read_delayed(self, fsm, global_addr, delay):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1
        delay_count = self.m.TmpReg(self.addrwidth, initval=0, prefix='delay_count')

        # state 0
        req_cond = fsm.here
        ack = self.read_request(global_addr, global_size, cond=req_cond)
        fsm(
            delay_count(delay)
        )
        fsm.If(ack).goto_next()

        # state 1
        done = vtypes.Ands(self.raddr.arvalid, self.raddr.arready)
        fsm.If(done).goto_next()

        # state 2
        fsm.If(delay_count > 0)(
            delay_count.dec()
        )
        fsm.If(delay_count == 0).goto_next()

        # state 3
        rcond = fsm.here
        rdata = self.m.TmpReg(self.datawidth, initval=0,
                              signed=True, prefix='axim_rdata')
        _ = self.read_data(cond=rcond)
        fsm.If(self.rdata.rvalid)(
            rdata(self.rdata.rdata)
        )
        fsm.If(self.rdata.rvalid).goto_next()

        return rdata

    def write_delayed(self, fsm, global_addr, value, delay):
        if self.use_global_base_addr:
            global_addr = self.global_base_addr + global_addr

        global_size = 1
        delay_count = self.m.TmpReg(self.addrwidth, initval=0, prefix='delay_count')

        # state 0
        req_cond = fsm.here
        ack = self.write_request(global_addr, global_size, cond=req_cond)
        fsm(
            delay_count(delay)
        )
        fsm.If(ack).goto_next()

        # state 1
        done = vtypes.Ands(self.waddr.awvalid, self.waddr.awready)
        fsm.If(done).goto_next()

        # state 2
        fsm.If(delay_count > 0)(
            delay_count.dec()
        )
        fsm.If(delay_count == 0).goto_next()

        # state 3
        wcond = fsm.here
        wdata = value
        _ = self.write_data(wdata, cond=wcond)
        ack = vtypes.Ors(self.wdata.wready, vtypes.Not(self.wdata.wvalid))
        fsm.If(ack).goto_next()

        # state 4
        done = vtypes.Ands(self.wdata.wvalid, self.wdata.wready)
        fsm.If(done).goto_next()

        # state 5
        res = self.write_completed()
        fsm.If(res).goto_next()
