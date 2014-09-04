module circuit1 (
  output [0:0] c_out,
  output [0:0] sigma,
  input [0:0] a,
  input [0:0] b,
  input [0:0] c_in
);

wire [0:0] xor1_out = a ^ b;
wire [0:0] nand1_out = ~ (a & b);
wire [0:0] nand2_out = ~ (c_in & xor1_out);

assign sigma = c_in ^ xor1_out;
assign c_out = ~ (nand1_out & nand2_out);

endmodule
