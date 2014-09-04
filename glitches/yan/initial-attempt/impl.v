// The RealIntent implimentation of a glitchy Mux 
// Yan 2014/08/11

module implRI(
dataA,
dataB,
a0,
sel,
mux_out
);

input dataA, dataB, a0, sel;
output mux_out;
wire mux_out;

assign mux_out = (dataB & dataA & a0) | (sel & dataA & dataB & ~a0) | (a0 & ~dataB & dataA & ~sel) | (~dataA & ~sel & a0);

endmodule
