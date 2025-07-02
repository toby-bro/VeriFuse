module case_unique_casez_reordered_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique casez ({case_expr[0], case_inside_val[3:2], case_expr[1]})
            4'b1?0?: internal_out = 30;
            4'b?101: internal_out = 31;  
            4'b0?1?: internal_out = 32;
            4'b1?1?: internal_out = 33;  
            4'b?111: internal_out = 34;  
        endcase
    end
endmodule

