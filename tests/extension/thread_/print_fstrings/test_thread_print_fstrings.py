from __future__ import absolute_import
from __future__ import print_function
import veriloggen
import thread_print_fstrings

expected_verilog = """
module test
(

);

  reg CLK;
  reg RST;
  wire [8-1:0] LED;

  blinkled
  uut
  (
    .CLK(CLK),
    .RST(RST),
    .LED(LED)
  );


  initial begin
    CLK = 0;
    forever begin
      #5 CLK = !CLK;
    end
  end


  initial begin
    RST = 0;
    #100;
    RST = 1;
    #100;
    RST = 0;
    #50000;
    $finish;
  end


endmodule



module blinkled
(
  input CLK,
  input RST,
  output reg [8-1:0] LED
);

  reg [10-1:0] CNT;
  reg [32-1:0] th_blink;
  localparam th_blink_init = 0;
  localparam th_blink_1 = 1;
  localparam th_blink_2 = 2;
  localparam th_blink_3 = 3;
  localparam th_blink_4 = 4;
  localparam th_blink_5 = 5;
  localparam th_blink_6 = 6;
  localparam th_blink_7 = 7;
  localparam th_blink_8 = 8;
  localparam th_blink_9 = 9;
  localparam th_blink_10 = 10;
  localparam th_blink_11 = 11;

  always @(posedge CLK) begin
    if(RST) begin
      th_blink <= th_blink_init;
      LED <= 0;
      CNT <= 0;
    end else begin
      case(th_blink)
        th_blink_init: begin
          th_blink <= th_blink_1;
        end
        th_blink_1: begin
          $display("Hello, world!");
          th_blink <= th_blink_2;
        end
        th_blink_2: begin
          if(1) begin
            th_blink <= th_blink_3;
          end else begin
            th_blink <= th_blink_11;
          end
        end
        th_blink_3: begin
          LED <= LED + 1;
          th_blink <= th_blink_4;
        end
        th_blink_4: begin
          CNT <= CNT + 3;
          th_blink <= th_blink_5;
        end
        th_blink_5: begin
          if(LED % 70 == 0) begin
            th_blink <= th_blink_6;
          end else begin
            th_blink <= th_blink_10;
          end
        end
        th_blink_6: begin
          $display("");
          th_blink <= th_blink_7;
        end
        th_blink_7: begin
          $display("led = %0d (%b)", LED, LED);
          th_blink <= th_blink_8;
        end
        th_blink_8: begin
          $display("cnt = %0d (%b)", CNT, CNT);
          th_blink <= th_blink_9;
        end
        th_blink_9: begin
          $display("cnt + led = %d", (CNT + LED));
          th_blink <= th_blink_10;
        end
        th_blink_10: begin
          th_blink <= th_blink_2;
        end
      endcase
    end
  end


endmodule
"""


def test():
    veriloggen.reset()
    test_module = thread_print_fstrings.mkTest()
    code = test_module.to_verilog()

    from pyverilog.vparser.parser import VerilogParser
    from pyverilog.ast_code_generator.codegen import ASTCodeGenerator
    parser = VerilogParser()
    expected_ast = parser.parse(expected_verilog)
    codegen = ASTCodeGenerator()
    expected_code = codegen.visit(expected_ast)

    assert(expected_code == code)

test()
