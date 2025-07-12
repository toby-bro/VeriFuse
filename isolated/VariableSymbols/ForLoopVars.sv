module ForLoopVars (
    input logic [3:0] limit,
    output logic [7:0] sum
);
    logic [7:0] temp_sum;
    always_comb begin
        temp_sum = 8'b0;
        for (logic [3:0] i = 0; i < limit; i++) begin
            temp_sum = temp_sum + i;
        end
        for (int i_int = 0, j_var = i_int; i_int < limit; i_int++) begin
            temp_sum = temp_sum + j_var;
        end
        sum = temp_sum;
    end
endmodule

