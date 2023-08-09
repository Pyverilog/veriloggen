from __future__ import absolute_import
from __future__ import print_function
import veriloggen
import stub_str_multiple


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
"""


def test():
    veriloggen.reset()
    test_module = stub_str_multiple.mkTop()
    code = test_module.to_verilog()

    from pyverilog.vparser.parser import VerilogParser
    from pyverilog.ast_code_generator.codegen import ASTCodeGenerator
    parser = VerilogParser()
    expected_ast = parser.parse(expected_verilog)
    codegen = ASTCodeGenerator()
    expected_code = codegen.visit(expected_ast)

    assert(expected_code == code)
