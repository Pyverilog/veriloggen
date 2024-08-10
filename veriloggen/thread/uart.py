from __future__ import absolute_import
from __future__ import print_function

import math
import veriloggen.core.vtypes as vtypes
from veriloggen.core.module import Module
from veriloggen.core.submodule import Submodule
from veriloggen.fsm.fsm import FSM

from .ttypes import _MutexFunction


class UartTx(Submodule, _MutexFunction):
    __intrinsics__ = {'send': '_intrinsic_send'} | _MutexFunction.__intrinsics__

    def __init__(self, m, name, prefix, clk, rst, txd=None,
                 arg_params=None, arg_ports=None,
                 as_io=None, as_wire=None,
                 baudrate=19200, clockfreq=100 * 1000 * 1000):

        if arg_ports is None:
            arg_ports = []

        arg_ports.insert(0, ('CLK', clk))
        arg_ports.insert(1, ('RST', rst))

        if txd is not None:
            arg_ports.insert(2, ('txd', txd))

        moddef = mkUartTx(baudrate, clockfreq)

        Submodule.__init__(self, m, moddef, name, prefix,
                           arg_params=arg_params, arg_ports=arg_ports,
                           as_io=as_io, as_wire=as_wire)

        self.tx_din = self['din']
        self.tx_enable = self['enable']
        self.tx_enable.initval = 0
        self.tx_ready = self['ready']

        self.mutex = None

    def _intrinsic_send(self, fsm, value):
        fsm(
            self.tx_din(value),
            self.tx_enable(1)
        )
        fsm.goto_next()
        fsm(
            self.tx_enable(0)
        )
        fsm.goto_next()
        fsm.If(self.tx_ready).goto_next()

    def send(self, value):
        raise NotImplementedError("Only the intrinsic method is implemented.")


class UartRx(Submodule, _MutexFunction):
    __intrinsics__ = {'recv': '_intrinsic_recv'} | _MutexFunction.__intrinsics__

    def __init__(self, m, name, prefix, clk, rst, rxd=None,
                 arg_params=None, arg_ports=None,
                 as_io=None, as_wire=None,
                 baudrate=19200, clockfreq=100 * 1000 * 1000):

        if arg_ports is None:
            arg_ports = []

        arg_ports.insert(0, ('CLK', clk))
        arg_ports.insert(1, ('RST', rst))

        if rxd is not None:
            arg_ports.insert(2, ('rxd', rxd))

        moddef = mkUartRx(baudrate, clockfreq)
        Submodule.__init__(self, m, moddef, name, prefix,
                           arg_params=arg_params, arg_ports=arg_ports,
                           as_io=as_io, as_wire=as_wire)

        self.rx_dout = self['dout']
        self.rx_valid = self['valid']

        self.mutex = None

    def _intrinsic_recv(self, fsm):
        ret = fsm.m.TmpReg(self.rx_dout.width)
        fsm.If(self.rx_valid)(
            ret(self.rx_dout)
        )
        fsm.Then().goto_next()
        return ret

    def recv(self):
        raise NotImplementedError("Only the intrinsic method is implemented.")


def mkUartTx(baudrate=19200, clockfreq=100 * 1000 * 1000):
    m = Module("UartTx")
    waitnum = int(clockfreq / baudrate)

    clk = m.Input('CLK')
    rst = m.Input('RST')

    din = m.Input('din', 8)
    enable = m.Input('enable')
    ready = m.OutputReg('ready', initval=1)
    txd = m.OutputReg('txd', initval=1)

    fsm = FSM(m, 'fsm', clk, rst)

    mem = m.TmpReg(9, initval=0)
    waitcount = m.TmpReg(int(math.log(waitnum, 2)) + 1, initval=0)

    fsm(
        waitcount(waitnum - 1),
        txd(1),
        mem(vtypes.Cat(din, vtypes.Int(0, 1)))
    )

    fsm.If(enable)(
        ready(0)
    )

    fsm.Then().goto_next()

    for i in range(10):
        fsm.If(waitcount > 0)(
            waitcount.dec()
        ).Else(
            txd(mem[0]),
            mem(vtypes.Cat(vtypes.Int(1, 1), mem[1:9])),
            waitcount(waitnum - 1)
        )
        fsm.Then().goto_next()

    fsm(
        ready(1)
    )

    fsm.goto_init()

    fsm.make_always()

    return m


def mkUartRx(baudrate=19200, clockfreq=100 * 1000 * 1000):
    m = Module("UartRx")
    waitnum = int(clockfreq / baudrate)

    clk = m.Input('CLK')
    rst = m.Input('RST')

    rxd = m.Input('rxd')
    dout = m.OutputReg('dout', 8, initval=0)
    valid = m.OutputReg('valid', initval=0)

    fsm = FSM(m, 'fsm', clk, rst)

    mem = m.TmpReg(9, initval=0)
    waitcount = m.TmpReg(int(math.log(waitnum, 2)) + 1, initval=0)

    fsm(
        valid(0),
        waitcount(int(waitnum / 2) - 1),
        mem(vtypes.Cat(rxd, mem[1:9]))
    )

    fsm.If(rxd == 0).goto_next()

    for i in range(10):
        if i == 0:  # check the start bit again
            fsm.If(vtypes.Ands(waitcount == 1, rxd != 0)).goto_init()

        fsm.If(waitcount > 0)(
            waitcount.dec()
        ).Else(
            mem(vtypes.Cat(rxd, mem[1:9])),
            waitcount(waitnum - 1)
        )
        fsm.Then().goto_next()

    fsm(
        valid(1),
        dout(mem[0:9])
    )

    fsm.goto_init()

    fsm.make_always()

    return m
