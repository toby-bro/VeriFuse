module mod_split_comb (
    input logic [7:0] data_in,
    input logic enable,
    output logic [7:0] out_a,
    output logic [7:0] out_b
);
    logic [7:0]  split_comb_var;
    logic [7:0] other_comb_var;
    always_comb begin
        split_comb_var = 8'b0; 
        other_comb_var = 8'b0;
        if (enable) begin
            split_comb_var = data_in;
            other_comb_var = data_in + 1;
        end
        out_a = split_comb_var;
        out_b = other_comb_var;
    end
endmodule

