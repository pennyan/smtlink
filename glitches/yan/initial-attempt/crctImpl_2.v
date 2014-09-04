// Version 2 glitch free implementation
// of a mux
// Yan 2014/08/11

module crctImpl_2(
dataA,
dataB,
a0,
sel,
mux_out
);

input dataA, dataB, a0, sel;
output mux_out;
wire mux_out;

assign mux_out = ~(~(a0 & ~sel) & ~( (dataA & dataB) & sel));

endmodule
