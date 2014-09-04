//
// A mux using is statement at RTL level
// Adapted from 
// http://asic-world.com/examples/verilog/mux.html
// Yan 2014/08/11

module specIf(
dataA,
dataB,
a0,
sel,
mux_out
);

input dataA, dataB, a0, sel;
output mux_out;
reg mux_out;

always @ (sel or (dataA & dataB) or a0)
begin: MUX
if (sel == 1'b1) begin
  mux_out = (dataA & dataB);
end else begin
  mux_out = a0;
end
end

endmodule
