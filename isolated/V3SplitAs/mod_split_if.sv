module mod_split_if (
    input logic clk,
    input logic reset,
    input logic cond,
    input logic [7:0] data_in,
    output logic [7:0] out_if_a,
    output logic [7:0] out_if_b
);
    logic [7:0]  split_if_var;
    logic [7:0] other_if_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var <= 8'b0;
            other_if_var <= 8'b0;
        end else begin
            if (cond) begin
                split_if_var <= data_in;
                other_if_var <= data_in + 3;
            end else begin
                split_if_var <= data_in - 1;
                other_if_var <= data_in - 2;
            end
        end
    end
    always_comb begin
        out_if_a = split_if_var;
        out_if_b = other_if_var;
    end
endmodule

