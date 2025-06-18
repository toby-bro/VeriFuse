module wide_loop (
    input logic i_control,
    input logic [15:0] i_data,
    output logic [15:0] o_result
);
    logic [15:0] r_temp1;
    logic [15:0] r_temp2;
    always_comb begin
        r_temp1 = r_temp2 + i_data;
        r_temp2 = r_temp1 ^ {16{i_control}};
        o_result = r_temp1 & r_temp2;
    end
endmodule

