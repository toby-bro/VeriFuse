module HandleSystemFunctionsAndCasex (
    output logic [3:0] o_countbits,
    output logic [1:0] o_case_result,
    input logic [3:0] i_val_sf,
    input logic [2:0] i_val_case,
    output logic o_isunknown
);
    assign o_isunknown = $isunknown(i_val_sf);
    assign o_countbits = $countbits(1, i_val_sf);
    always_comb begin
        casez (i_val_case)
            3'b1?0: o_case_result = 2'b01;
            3'b??1: o_case_result = 2'b10;
            default: o_case_result = 2'b11;
        endcase
    end
endmodule

