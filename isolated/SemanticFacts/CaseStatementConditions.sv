module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case
);
    always_comb begin
        case (selector)
            2'b00: out_case = data_c;
            2'b01: out_case = data_c + 1;
            2'b10: out_case = data_c + 2;
            default: out_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case = data_c + 10;
            2'b1?: out_case = data_c + 20;
            default: out_case = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case = data_c - 1;
            2'b1?: out_case = data_c - 2;
            default: out_case = 4'bxxxx;
        endcase
    end
endmodule

