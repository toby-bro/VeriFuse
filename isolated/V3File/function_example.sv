module function_example (
    input logic enable_func,
    input logic [7:0] val_in,
    output logic [7:0] func_out
);
    function automatic logic [7:0] double_value (input logic [7:0] input_val);
        return input_val * 2;
    endfunction 
    always_comb begin
        if (enable_func) begin
            func_out = double_value(val_in); 
        end else begin
            func_out = 8'h00;
        end
    end
endmodule

