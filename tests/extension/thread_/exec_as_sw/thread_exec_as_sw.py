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
    led = m.OutputReg('LED', 8, initval=0)

    datawidth = 32
    addrwidth = 10
    myram = vthread.RAM(m, 'myram', clk, rst, datawidth, addrwidth)

    def blink(times):
        all_ok = True

        write_sum = 0
        for i in range(times):
            wdata = i
            myram.write(i, wdata)
            write_sum += wdata
            print('wdata = %d' % wdata)

        read_sum = 0
        for i in range(times):
            rdata = myram.read(i)
            read_sum += rdata
            print('rdata = %d' % rdata)
            #if vthread.verilog.NotEql(rdata, i):
            if rdata != i:
                all_ok = False

        print('read_sum = %d' % read_sum)

        #if vthread.verilog.NotEql(read_sum, write_sum):
        if read_sum != write_sum:
            all_ok = False

        led.value = 0
        for i in range(times):
            led.value += 1
            print(led, i)

        if all_ok and led == times:
            print('# verify: PASSED')
        else:
            print('# verify: FAILED')

    # as SW
    print("as SW")
    blink(100)

    print("as HW")

    # as HW
    th = vthread.Thread(m, 'th_blink', clk, rst, blink)
    fsm = th.start(100)

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
        Delay(1000000),
        Systask('finish'),
    )

    return m


def run(filename='tmp.v', simtype='iverilog', outputfile=None):

    if outputfile is None:
        outputfile = os.path.splitext(os.path.basename(__file__))[0] + '.out'

    test = mkTest()

    if filename is not None:
        test.to_verilog(filename)

    sim = simulation.Simulator(test, sim=simtype)
    rslt = sim.run(outputfile=outputfile)

    return rslt


if __name__ == '__main__':
    rslt = run(filename='tmp.v')
    print(rslt)
