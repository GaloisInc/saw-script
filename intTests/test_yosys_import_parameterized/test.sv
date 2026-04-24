module dff #(parameter WIDTH=1)
  (input logic              clk,
   input logic [WIDTH-1:0]  d,
   output logic [WIDTH-1:0] q);

   always_ff @(posedge clk) begin
      q <= d;
   end

endmodule // dff

module main
  (input logic         clk,
   input logic [5:0]   x,
   input logic [9:0]   y,
   output logic [15:0] z);

   wire logic [5:0] q_x;
   wire logic [9:0] q_y;

   dff #(6) inst1 (.clk(clk), .d(x), .q(q_x));
   dff #(10) inst2 (.clk(clk), .d(y), .q(q_y));

   assign z = {q_x, q_y};

endmodule // main
