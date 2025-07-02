module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

