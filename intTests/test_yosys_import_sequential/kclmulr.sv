//////////////////////////////////////////////////////////////////////
// Karatsuba carryless multiplier with synchronous reset

module kclmul4r
  (input logic        clk,
   input logic        reset,
   input logic [3:0]  x,
   input logic [3:0]  y,
   output logic [7:0] z);

   logic [3:0] x_r, y_r;
   always_ff @(posedge clk) begin
      x_r <= reset ? '0 : x;
      y_r <= reset ? '0 : y;
   end

   logic [3:0][3:0] pp;
   for (genvar i = 0; i < 4; i++) begin
      assign pp[i] = x_r[i] ? y_r : 4'b0;
   end

   wire logic [4:0][7:0] p;
   assign p[0] = 8'b0;
   for (genvar i = 0; i < 4; i++) begin
      assign p[i+1] = p[i] ^ (pp[i] << i);
   end

   assign z = reset ? '0 : p[4];

endmodule // kcmlul4r

module kclmul8r
  (input logic         clk,
   input logic         reset,
   input logic [7:0]   x,
   input logic [7:0]   y,
   output logic [15:0] z);

   wire logic [3:0] xl, xh, yl, yh;
   assign xl = x[3:0];
   assign xh = x[7:4];
   assign yl = y[3:0];
   assign yh = y[7:4];

   wire logic [7:0] z1, z2, z3;

   kclmul4r m1 (.clk(clk), .reset(reset), .x(xl), .y(yl), .z(z1));
   kclmul4r m2 (.clk(clk), .reset(reset), .x(xh), .y(yh), .z(z2));
   kclmul4r m3 (.clk(clk), .reset(reset), .x(xl^xh), .y(yl^yh), .z(z3));

   wire logic [15:0] term0, term1;
   assign term0 = {z2, z1};
   assign term1 = {4'b0, z1 ^ z2 ^ z3, 4'b0};

   assign z = reset ? '0 : term0 ^ term1;

endmodule // kclmul8r

module kclmul16r
  (input logic         clk,
   input logic         reset,
   input logic [15:0]  x,
   input logic [15:0]  y,
   output logic [31:0] z);

   wire logic [7:0] xl, xh, yl, yh;
   assign xl = x[7:0];
   assign xh = x[15:8];
   assign yl = y[7:0];
   assign yh = y[15:8];

   wire logic [15:0] z1, z2, z3;

   kclmul8r m1 (.clk(clk), .reset(reset), .x(xl), .y(yl), .z(z1));
   kclmul8r m2 (.clk(clk), .reset(reset), .x(xh), .y(yh), .z(z2));
   kclmul8r m3 (.clk(clk), .reset(reset), .x(xl^xh), .y(yl^yh), .z(z3));

   wire logic [31:0] term0, term1;
   assign term0 = {z2, z1};
   assign term1 = {8'b0, z1 ^ z2 ^ z3, 8'b0};

   assign z = reset ? '0 : term0 ^ term1;

endmodule // kclmul16r
