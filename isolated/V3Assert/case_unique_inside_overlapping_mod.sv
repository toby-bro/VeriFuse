module case_unique_inside_overlapping_mod (
    input logic [3:0] case_inside_val,
    input logic [3:0] range_end,
    input logic [3:0] range_start,
    output logic [4:0] internal_out
);
    always @* begin
        unique case (case_inside_val)
            case_inside_val inside {[range_start:range_end]}: internal_out = 16;
            case_inside_val inside {4'd0, 4'd1, 4'd2}: internal_out = 17;  
            case_inside_val inside {4'd8, 4'd9}: internal_out = 18;
            case_inside_val inside {[4'd7:4'd10]}: internal_out = 19;  
            case_inside_val inside {4'd15}: internal_out = 20;  
            default: internal_out = 21;  
        endcase
    end
endmodule

