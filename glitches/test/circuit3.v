module circuit3 (
  output c_out,
  output sigma,
  input a,
  input b,
  input c_in
);

wire nand1_out = ~ (a & b);
wire nand2_out = ~ (b & c_in);
wire nand3_out = ~ (a & c_in);
wire nor1_out = ~ (a | b | c_in);
wire nand4_out = ~ (a & b & c_in);

assign c_out = ~ (nand1_out & nand2_out & nand3_out);

wire nor2_out = ~ (c_out | nor1_out);

assign sigma = ~ (nor2_out & nand4_out);

endmodule
