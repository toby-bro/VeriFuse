module case_full_parallel_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

