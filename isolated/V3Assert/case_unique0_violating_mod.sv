module case_unique0_violating_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  
            2'b?1: internal_out = 10; 
            2'b00: internal_out = 11; 
        endcase
    end
endmodule

