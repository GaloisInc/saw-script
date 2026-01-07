module shift_dyn_idx (
    input  logic [3:0]   idx,
    output logic [7:0]   out
);
    always_comb begin
        out = '0;
        out[idx] = '1;
    end
endmodule

module shift_dyn_idx_signed (
    input  signed [3:0]   idx,
    output logic [7:0]   out
);
    always_comb begin
        out = '0;
        out[idx] = '1;
    end
endmodule

module shift_sshr_trunc (
    input  signed [15:0] a,
    input  [3:0] b,
    output logic [7:0] out
);
    assign out = a >>> b;
endmodule

module shift_sshr_ext (
    input  signed [3:0] a,
    input  [3:0] b,
    output logic [7:0] out
);
    assign out = a >>> b;
endmodule

module shift_dyn (
    input  signed [4:0]  idx,
    input  logic [7:0]   inp,
    output logic [7:0]   out
);
    always_comb begin
        out = inp >>> $signed(idx);
    end
endmodule
