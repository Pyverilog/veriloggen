from __future__ import absolute_import
from __future__ import print_function

import veriloggen.core.vtypes as vtypes
import veriloggen.types.util as util
import veriloggen.types.axi as axi
from veriloggen.fsm.fsm import FSM

from .ttypes import _MutexFunction


class AXIS(axi.AxiSlave, _MutexFunction):
    __intrinsics__ = _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 waddr_id_width=0, wdata_id_width=0, wresp_id_width=0,
                 raddr_id_width=0, rdata_id_width=0,
                 waddr_user_width=2, wdata_user_width=0, wresp_user_width=0,
                 raddr_user_width=2, rdata_user_width=0,
                 wresp_user_mode=axi.xUSER_DEFAULT,
                 rdata_user_mode=axi.xUSER_DEFAULT,
                 noio=False):

        axi.AxiSlave.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                              waddr_id_width, wdata_id_width, wresp_id_width,
                              raddr_id_width, rdata_id_width,
                              waddr_user_width, wdata_user_width, wresp_user_width,
                              raddr_user_width, rdata_user_width,
                              wresp_user_mode,
                              rdata_user_mode,
                              noio)
        self.mutex = None


class AXISLite(axi.AxiLiteSlave, _MutexFunction):
    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 noio=False):

        axi.AxiLiteSlave.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                                  noio)
        self.mutex = None


class AXISRegister(AXIS):
    __intrinsics__ = {'read': 'read',
                      'write': 'write',
                      'write_flag': 'write_flag',
                      'wait': 'wait',
                      'wait_flag': 'wait_flag',
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 waddr_id_width=0, wdata_id_width=0, wresp_id_width=0,
                 raddr_id_width=0, rdata_id_width=0,
                 waddr_user_width=2, wdata_user_width=0, wresp_user_width=0,
                 raddr_user_width=2, rdata_user_width=0,
                 wresp_user_mode=axi.xUSER_DEFAULT,
                 rdata_user_mode=axi.xUSER_DEFAULT,
                 noio=False, length=4, fsm_as_module=False):

        AXIS.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                      waddr_id_width, wdata_id_width, wresp_id_width,
                      raddr_id_width, rdata_id_width,
                      waddr_user_width, wdata_user_width, wresp_user_width,
                      raddr_user_width, rdata_user_width,
                      wresp_user_mode,
                      rdata_user_mode,
                      noio)

        self.fsm_as_module = fsm_as_module

        if not isinstance(length, int):
            raise TypeError("length must be 'int', not '%s'" %
                            str(type(length)))

        self.register = [self.m.Reg('_'.join(['', self.name, 'register', '%d' % i]),
                                    width=self.datawidth, initval=0, signed=True)
                         for i in range(length)]
        self.flag = [self.m.Reg('_'.join(['', self.name, 'flag', '%d' % i]), initval=0)
                     for i in range(length)]
        self.resetval = [self.m.Reg('_'.join(['', self.name, 'resetval', '%d' % i]),
                                    width=self.datawidth, initval=0, signed=True)
                         for i in range(length)]
        self.length = length
        self.maskwidth = self.m.Localparam('_'.join(['', self.name, 'maskwidth']),
                                           util.log2(length))
        self.mask = self.m.Localparam('_'.join(['', self.name, 'mask']),
                                      vtypes.Repeat(vtypes.Int(1, 1), self.maskwidth))
        self.shift = self.m.Localparam('_'.join(['', self.name, 'shift']),
                                       util.log2(self.datawidth // 8))

        self._set_register_full_fsm()

    def _set_register_full_fsm(self):
        fsm = FSM(self.m, '_'.join(['', self.name, 'register_fsm']),
                  self.clk, self.rst, as_module=self.fsm_as_module)

        # request
        addr, length, readvalid, writevalid = self.pull_request(cond=fsm)

        rcount = self.m.TmpReg(self.burst_size_width + 1, initval=0,
                               prefix='axis_rcount')
        rlast = self.m.TmpReg(initval=0, prefix='axis_rlast')
        maskaddr = self.m.TmpReg(self.maskwidth, initval=0, prefix='axis_maskaddr')

        fsm.If(readvalid)(
            rcount(length),
            rlast(length <= 1)
        )
        fsm.If(vtypes.Ors(readvalid, writevalid))(
            maskaddr((addr >> self.shift) & self.mask),
        )

        init_state = fsm.current

        # read
        read_state = fsm.current + 1
        fsm.If(readvalid).goto_from(init_state, read_state)
        fsm.set_index(read_state)

        rdata = self.m.TmpWire(self.datawidth, signed=True, prefix='axis_rdata')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.register)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        rdata.assign(rval)

        flag = self.m.TmpWire(prefix='axis_flag')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.flag)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        flag.assign(rval)

        resetval = self.m.TmpWire(self.datawidth, signed=True, prefix='axis_resetval')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.resetval)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        resetval.assign(rval)

        ack = self.push_read_data(rdata, rlast, cond=fsm)

        fsm.If(ack)(
            maskaddr.inc(),
            rcount.dec(),
            rlast(rcount <= 1)
        )

        # flag reset
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, ack, flag, maskaddr == i)(
                self.register[i](resetval),
                self.flag[i](0)
            )

        fsm.If(ack, rlast).goto_init()

        # write
        write_state = fsm.current + 1
        fsm.If(writevalid).goto_from(init_state, write_state)
        fsm.set_index(write_state)

        data, mask, valid, last = self.pull_write_data(cond=fsm)

        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, valid, maskaddr == i)(
                self.register[i](data)
            )

        fsm.If(valid)(
            maskaddr.inc()
        )
        fsm.If(valid, last).goto_init()

    def read(self, fsm, addr):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)
        return rval

    def write(self, fsm, addr, value):
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, addr == i)(
                self.register[i](value),
                self.flag[i](0)
            )
        fsm.goto_next()

    def write_flag(self, fsm, addr, value, resetvalue=0):
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, addr == i)(
                self.register[i](value),
                self.flag[i](1),
                self.resetval[i](resetvalue)
            )
        fsm.goto_next()

    def wait(self, fsm, addr, value, polarity=True):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)

        if polarity:
            wait_cond = (rval == value)
        else:
            wait_cond = (rval != value)

        fsm.If(wait_cond).goto_next()

    def wait_flag(self, fsm, addr, value, resetvalue=0, polarity=True):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)

        if polarity:
            wait_cond = (rval == value)
        else:
            wait_cond = (rval != value)

        state_cond = fsm.state == fsm.current

        # flag reset
        for i, r in enumerate(self.register):
            self.seq.If(wait_cond, state_cond, addr == i)(
                self.register[i](resetvalue)
            )

        fsm.If(wait_cond).goto_next()


class AXISLiteRegister(AXISLite):
    __intrinsics__ = {'read': 'read',
                      'write': 'write',
                      'write_flag': 'write_flag',
                      'wait': 'wait',
                      'wait_flag': 'wait_flag',
                      } | _MutexFunction.__intrinsics__

    def __init__(self, m, name, clk, rst, datawidth=32, addrwidth=32,
                 noio=False, length=4, fsm_as_module=False):

        AXISLite.__init__(self, m, name, clk, rst, datawidth, addrwidth,
                          noio)

        self.fsm_as_module = fsm_as_module

        if not isinstance(length, int):
            raise TypeError("length must be 'int', not '%s'" %
                            str(type(length)))

        self.register = [self.m.Reg('_'.join(['', self.name, 'register', '%d' % i]),
                                    width=self.datawidth, initval=0, signed=True)
                         for i in range(length)]
        self.flag = [self.m.Reg('_'.join(['', self.name, 'flag', '%d' % i]), initval=0)
                     for i in range(length)]
        self.resetval = [self.m.Reg('_'.join(['', self.name, 'resetval', '%d' % i]),
                                    width=self.datawidth, initval=0, signed=True)
                         for i in range(length)]
        self.length = length
        self.maskwidth = self.m.Localparam('_'.join(['', self.name, 'maskwidth']),
                                           util.log2(length))
        self.mask = self.m.Localparam('_'.join(['', self.name, 'mask']),
                                      vtypes.Repeat(vtypes.Int(1, 1), self.maskwidth))
        self.shift = self.m.Localparam('_'.join(['', self.name, 'shift']),
                                       util.log2(self.datawidth // 8))

        self._set_register_lite_fsm()

    def _set_register_lite_fsm(self):
        fsm = FSM(self.m, '_'.join(['', self.name, 'register_fsm']),
                  self.clk, self.rst, as_module=self.fsm_as_module)

        # request
        addr, readvalid, writevalid = self.pull_request(cond=fsm)

        maskaddr = self.m.TmpReg(self.maskwidth, initval=0, prefix='axis_maskaddr')
        fsm.If(vtypes.Ors(readvalid, writevalid))(
            maskaddr((addr >> self.shift) & self.mask),
        )

        init_state = fsm.current

        # read
        read_state = fsm.current + 1
        fsm.If(readvalid).goto_from(init_state, read_state)
        fsm.set_index(read_state)

        rdata = self.m.TmpWire(self.datawidth, signed=True, prefix='axislite_rdata')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.register)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        rdata.assign(rval)

        flag = self.m.TmpWire(prefix='axislite_flag')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.flag)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        flag.assign(rval)

        resetval = self.m.TmpWire(self.datawidth, signed=True, prefix='axislite_resetval')
        pat = [(maskaddr == i, r) for i, r in enumerate(self.resetval)]
        pat.append((None, vtypes.IntX()))
        rval = vtypes.PatternMux(pat)
        resetval.assign(rval)

        ack = self.push_read_data(rdata, cond=fsm)

        # flag reset
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, ack, flag, maskaddr == i)(
                self.register[i](resetval),
                self.flag[i](0)
            )

        fsm.If(ack).goto_next()

        done = vtypes.Ands(self.rdata.rready, self.rdata.rvalid)
        fsm.If(done).goto_init()

        # write
        write_state = fsm.current + 1
        fsm.If(writevalid).goto_from(init_state, write_state)
        fsm.set_index(write_state)

        data, mask, valid = self.pull_write_data(cond=fsm)

        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, valid, maskaddr == i)(
                self.register[i](data)
            )

        fsm.If(valid).goto_next()

        done = vtypes.Ands(self.wresp.bready, self.wresp.bvalid)
        fsm.If(done).goto_init()

    def read(self, fsm, addr):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)
        return rval

    def write(self, fsm, addr, value):
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, addr == i)(
                self.register[i](value),
                self.flag[i](0)
            )
        fsm.goto_next()

    def write_flag(self, fsm, addr, value, resetvalue=0):
        state_cond = fsm.state == fsm.current
        for i, r in enumerate(self.register):
            self.seq.If(state_cond, addr == i)(
                self.register[i](value),
                self.flag[i](1),
                self.resetval[i](resetvalue)
            )
        fsm.goto_next()

    def wait(self, fsm, addr, value, polarity=True):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)

        if polarity:
            wait_cond = (rval == value)
        else:
            wait_cond = (rval != value)

        fsm.If(wait_cond).goto_next()

    def wait_flag(self, fsm, addr, value, resetvalue=0, polarity=True):
        if isinstance(addr, int):
            rval = self.register[addr]
        elif isinstance(addr, vtypes.Int):
            rval = self.register[addr.value]
        else:
            pat = [(addr == i, r) for i, r in enumerate(self.register)]
            pat.append((None, vtypes.IntX()))
            rval = vtypes.PatternMux(pat)

        if polarity:
            wait_cond = (rval == value)
        else:
            wait_cond = (rval != value)

        state_cond = fsm.state == fsm.current

        # flag reset
        for i, r in enumerate(self.register):
            self.seq.If(wait_cond, state_cond, addr == i)(
                self.register[i](resetvalue)
            )

        fsm.If(wait_cond).goto_next()
