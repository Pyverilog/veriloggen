from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import collections

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))))

from veriloggen import *

stubcode = """\


module blinkled #
(
  parameter WIDTH = 8
)
(
  input CLK,
  input RST,
  output reg [WIDTH-1:0] LED
);

  reg [32-1:0] count;

  always @(posedge CLK) begin
    if(RST) begin
      count <= 0;
    end else begin
      if(count == 1023) begin
        count <= 0;
      end else begin
        count <= count + 1;
      end
    end
  end


  always @(posedge CLK) begin
    if(RST) begin
      LED <= 0;
    end else begin
      if(count == 1023) begin
        LED <= LED + 1;
      end 
    end
  end


endmodule

"""


def mkLed():
    m = StubModule('blinkled', code=stubcode)
    return m


def mkTop():
    m = Module('top')
    width = m.Parameter('WIDTH', 8)
    clk = m.Input('CLK')
    rst = m.Input('RST')
    led0 = m.Output('LED0', width)
    led1 = m.Output('LED1', width)

    params0 = (width,)
    ports0 = (clk, rst, led0)
    m.Instance(mkLed(), 'inst_blinkled0', params0, ports0)

    params1 = (width,)
    ports1 = (clk, rst, led1)
    m.Instance(mkLed(), 'inst_blinkled1', params1, ports1)

    return m


if __name__ == '__main__':
    top = mkTop()
    verilog = top.to_verilog()
    print(verilog)
