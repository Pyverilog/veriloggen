from __future__ import absolute_import
from __future__ import print_function
import sys
import os

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))))

from veriloggen import *
import veriloggen.thread as vthread


def mkLed():
    m = Module('blinkled')
    clk = m.Input('CLK')
    rst = m.Input('RST')

    data = m.Reg('data', 8, initval=0)
    enable = m.Reg('enable', initval=0)
    ready = m.Wire('ready')
    ready.assign(1)

    def send(fsm, value):
        fsm(
            data(value),
            enable(1),
            Display("data = %d", value)
        )
        fsm.goto_next()
        fsm(
            enable(0)
        )
        fsm.goto_next()
        return 0

    def wait(fsm):
        fsm.If(ready).goto_next()
        return 0

    def blink(times):
        for i in range(times):
            data = i + 100
            send(data)
            wait()

    th = vthread.Thread(m, 'th_blink', clk, rst, blink)

    # add intrinsic functions
    th.add_intrinsic(send, 'send')
    th.add_intrinsic(wait, 'wait')

    fsm = th.start(10)

    return m


def mkTest():
    m = Module('test')

    # target instance
    led = mkLed()

    # copy paras and ports
    params = m.copy_params(led)
    ports = m.copy_sim_ports(led)

    clk = ports['CLK']
    rst = ports['RST']

    uut = m.Instance(led, 'uut',
                     params=m.connect_params(led),
                     ports=m.connect_ports(led))

    # vcd_name = os.path.splitext(os.path.basename(__file__))[0] + '.vcd'
    # simulation.setup_waveform(m, uut, dumpfile=vcd_name)
    simulation.setup_clock(m, clk, hperiod=5)
    init = simulation.setup_reset(m, rst, m.make_reset(), period=100)

    init.add(
        Delay(10000),
        Systask('finish'),
    )

    return m


if __name__ == '__main__':
    test = mkTest()
    verilog = test.to_verilog('tmp.v')
    print(verilog)

    sim = simulation.Simulator(test)
    rslt = sim.run()
    print(rslt)
