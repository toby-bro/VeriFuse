module mod_part_select (
    input wire [31:0] data_in,
    output logic [31:0] data_out
);
    logic [31:0] temp_reg;
    always_comb begin
        temp_reg[7:0] = data_in[7:0];
        temp_reg[15:8] = data_in[23:16];
        temp_reg[31:16] = data_in[15:0];
        temp_reg[0] = data_in[31];
        temp_reg[8] = data_in[0];
        data_out = temp_reg;
    end
endmodule

