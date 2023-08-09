from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import collections

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))))

from veriloggen import *


def mkTop():
    m = Module('top')
    width = m.Parameter('WIDTH', 8)
    clk = m.Input('CLK')
    rst = m.Input('RST')
    led0 = m.Output('LED0', width)
    led1 = m.Output('LED1', width)

    params0 = (width,)
    ports0 = (clk, rst, led0)
    m.Instance('blinkled', 'inst_blinkled0', params0, ports0)

    params1 = (width,)
    ports1 = (clk, rst, led1)
    m.Instance('blinkled', 'inst_blinkled1', params0, ports1)

    return m


if __name__ == '__main__':
    top = mkTop()
    verilog = top.to_verilog()
    print(verilog)
