// ex_ite.v
module ex_ite (
    input clk,
    input reset_n,

    output [1 : 0] res
);

  localparam ZERO = 0;
  localparam ONE = 1;
  localparam TWO = 2;

  reg [1 : 0] num;

  always @ (posedge clk)
    begin
      if (!reset_n)
        begin
          num <= ZERO;
        end
      else
        begin
          num <= res;
        end
    end

  always @*
    begin
      res  = ZERO;

      if (ZERO == num)
          begin
            res = ONE;
          end

      else if (ONE == num)
          begin
            res = TWO;
          end

      else if (TWO == num)
          begin
            res = ZERO;
          end
    end

endmodule
