module test
  (input logic        clk,
   input logic        arst_x,
   input logic        aload_y,
   input logic        load_z,
   input logic        en_z,
   input logic [7:0]  d,
   output logic [7:0] x,
   output logic [7:0] y,
   output logic [7:0] z
   );

   always_ff @(posedge clk, posedge arst_x) begin
      if (arst_x)
        x <= 8'd0;
      else
        x <= x + 1;
   end

   always_ff @(posedge clk, posedge aload_y) begin
      if (aload_y)
        y <= d;
      else
        y <= y + 1;
   end

   always_ff @(posedge clk) begin
      if (en_z)
        z <= load_z ? d : z + 1;
   end

endmodule // test
