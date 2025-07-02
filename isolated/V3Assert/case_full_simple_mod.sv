module case_full_simple_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full *)
        case (case_expr)
            2'b00: internal_out = 10;
            2'b01: internal_out = 11;
            2'b10: internal_out = 12;
            default: internal_out = 13;
        endcase
    end
endmodule

