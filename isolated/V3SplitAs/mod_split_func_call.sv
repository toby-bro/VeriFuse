module mod_split_func_call (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_func_a,
    output logic [7:0] out_func_b
);
    function automatic logic [7:0] dummy_func (input logic [7:0] val);
        return val + 5;
    endfunction
    logic [7:0]  split_func_var;
    logic [7:0] other_func_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_func_var <= 8'b0;
            other_func_var <= 8'b0;
        end else begin
            split_func_var <= dummy_func(data_in);
            other_func_var <= data_in + 1;
            if (data_in > 50) begin
                other_func_var <= dummy_func(data_in + 10);
            end
            out_func_a <= split_func_var;
            out_func_b <= other_func_var;
        end
    end
endmodule

