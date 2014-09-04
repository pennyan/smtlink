//
// A mux using assign statement at RTL level
// Adapted from 
// http://asic-world.com/examples/verilog/mux.html
// Yan 2014/08/11

module specAssign(
dataA,
dataB,
a0,
sel,
mux_out
);

input dataA, dataB, a0, sel;
output mux_out;
wire mux_out;

assign mux_out = (sel) ? (dataA & dataB) : a0;

endmodule
