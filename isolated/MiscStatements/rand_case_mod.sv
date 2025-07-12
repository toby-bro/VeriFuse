module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule

