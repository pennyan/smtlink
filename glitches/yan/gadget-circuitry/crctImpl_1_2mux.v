// Version 1 glitch free implementation
// of a mux
// Yan 2014/08/11

module crctImpl_1_2mux(
xx,
tt,
ff,
dataA_1,
dataA_2,
dataB,
a0,
sel,
mux_out
);

input xx, tt, ff, dataA_1, dataA_2, dataB, a0, sel;
output mux_out;
wire dataA;
wire mux_out;

assign dataA = (dataA_2) ? xx : ((dataA_1) ? tt : ff); 
assign mux_out = (a0 & ~sel) | ((dataA & dataB) & sel);

endmodule
