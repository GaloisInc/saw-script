// ex_case.v
module ex_case (
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

      case (num)
        ZERO:
          begin
            res = ONE;
          end

        ONE:
          begin
            res = TWO;
          end

        TWO:
          begin
            res = ZERO;
          end
      endcase
    end

endmodule // ex_case
