//
// A mux using assign statement at RTL level
// Adapted from 
// http://asic-world.com/examples/verilog/mux.html
// Yan 2014/08/11
//
// Added a little gadget to get dataA and dataB values
// from ACL2.

module specAssign_2mux(
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
assign mux_out = (sel) ? (dataA & dataB) : a0;

endmodule
