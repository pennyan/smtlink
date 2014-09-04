module circuit2 (
  output c_out,
  output sigma,
  input a,
  input b,
  input c_in
);

wire xnor1_out = ~ (a ^ b);
wire nand1_out = ~ (a & b);
wire nand2_out = ~ (xnor1_out & c_in);

assign sigma = ~ (c_in ^ xnor1_out);
assign c_out = ~ (nand1_out & nand2_out);

endmodule