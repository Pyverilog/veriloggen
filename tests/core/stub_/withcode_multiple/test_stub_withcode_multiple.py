from __future__ import absolute_import
from __future__ import print_function
import veriloggen
import stub_withcode_multiple

expected_verilog = """
module top #
(
  parameter WIDTH = 8
)
(
  input CLK,
  input RST,
  output [WIDTH-1:0] LED0,
  output [WIDTH-1:0] LED1
);


  blinkled
  #(
    WIDTH
  )
  inst_blinkled0
  (
    CLK,
    RST,
    LED0
  );


  blinkled
  #(
    WIDTH
  )
  inst_blinkled1
  (
    CLK,
    RST,
    LED1
  );


endmodule



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


def test():
    veriloggen.reset()
    test_module = stub_withcode_multiple.mkTop()
    code = test_module.to_verilog()

    from pyverilog.vparser.parser import VerilogParser
    from pyverilog.ast_code_generator.codegen import ASTCodeGenerator
    parser = VerilogParser()
    expected_ast = parser.parse(expected_verilog)
    codegen = ASTCodeGenerator()
    expected_code = codegen.visit(expected_ast)

    assert(expected_code == code)
