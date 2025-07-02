module case_unique0_inside_no_default_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 case (case_inside_val)
            case_inside_val inside {4'd10, 4'd11}: internal_out = 19;
            case_inside_val inside {4'd11, 4'd12}: internal_out = 20;  
            case_inside_val inside {[4'd10:4'd13]}: internal_out = 21;  
            case_inside_val inside {4'd14, 4'd15}: internal_out = 22;
            case_inside_val inside {4'd15}: internal_out = 23;  
        endcase
    end
endmodule

