//
// A mux using case statement at RTL level
// Adapted from 
// http://asic-world.com/examples/verilog/mux.html
// Yan 2014/08/11

module specCase(
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
case (sel)
  1'b0 : mux_out = a0;
  1'b1 : mux_out = (dataA & dataB);
endcase
end

endmodule
