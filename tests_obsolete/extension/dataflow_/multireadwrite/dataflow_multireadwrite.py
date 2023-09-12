from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import math

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))))

from veriloggen import *
import veriloggen.dataflow as dataflow


def mkMain(n=128, datawidth=32, numports=2):
    m = Module('main')

    clk = m.Input('CLK')
    rst = m.Input('RST')

    # variables
    x = dataflow.Variable('xdata', 'xvalid', 'xready', signed=False)
    y = dataflow.Variable('ydata', 'yvalid', 'yready', signed=False)
    z = x + y
    z.output('zdata', 'zvalid', 'zready')

    # synthesize dataflow
    df = dataflow.Dataflow(z)
    df.implement(m, clk, rst, aswire=True)
    # df.draw_graph()

    # write
    xfsm = FSM(m, 'xfsm', clk, rst)
    xcount = m.TmpReg(32, initval=0)

    xack = x.write(xcount, cond=xfsm)
    xfsm.If(xack)(
        xcount.inc()
    )
    xfsm.Then().If(xcount == 7).goto_next()

    xfsm.goto_next()
    xfsm.goto_next()
    xfsm.goto_next()
    xfsm.goto_next()

    xack = x.write(xcount, cond=xfsm)
    xfsm.If(xack)(
        xcount.inc()
    )
    xfsm.Then().If(xcount == 15).goto_next()

    xfsm.make_always()

    # write
    yfsm = FSM(m, 'yfsm', clk, rst)
    ycount = m.TmpReg(32, initval=0)

    yack = y.write(ycount, cond=yfsm)
    yfsm.If(yack)(
        ycount(ycount + 1)
    )
    yfsm.Then().If(ycount == 7).goto_next()

    yfsm.goto_next()
    yfsm.goto_next()
    yfsm.goto_next()
    yfsm.goto_next()
    yfsm.goto_next()
    yfsm.goto_next()

    yack = y.write(ycount, cond=yfsm)
    yfsm.If(yack)(
        ycount(ycount + 1)
    )
    yfsm.Then().If(ycount == 15).goto_next()

    yfsm.make_always()

    # read
    zfsm = FSM(m, 'zfsm', clk, rst)
    zcount = m.TmpReg(32, initval=0)

    zdata, zvalid = z.read(cond=zfsm)
    zfsm.If(zvalid)(
        Systask('display', "zfsm_%1d: zdata=%d", zfsm.state, zdata),
        zcount.inc()
    )

    zfsm.If(zcount == 8).goto_next()

    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()
    zfsm.goto_next()

    zdata, zvalid = z.read(cond=(zfsm, zcount < 32))  # dummy condition
    zfsm.If(zvalid)(
        Systask('display', "zfsm_%1d: zdata=%d", zfsm.state, zdata),
        zcount.inc()
    )

    zfsm.make_always()

    return m


def mkTest():
    m = Module('test')

    # target instance
    main = mkMain()

    # copy paras and ports
    params = m.copy_params(main)
    ports = m.copy_sim_ports(main)

    clk = ports['CLK']
    rst = ports['RST']

    uut = m.Instance(main, 'uut',
                     params=m.connect_params(main),
                     ports=m.connect_ports(main))

    vcd_name = os.path.splitext(os.path.basename(__file__))[0] + '.vcd'
    simulation.setup_waveform(m, uut, m.get_vars(), dumpfile=vcd_name)
    simulation.setup_clock(m, clk, hperiod=5)
    init = simulation.setup_reset(m, rst, m.make_reset(), period=100)

    init.add(
        Delay(1000 * 100),
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

    # sim.view_waveform()
