module MiscExpressions_ClockVar_Binding (
    input logic clk_in,
    input logic in_data,
    output logic clk_out_port,
    output logic out_data_read_input,
    output logic out_data_read_output_dummy
);
    logic clock_var_output;
    clocking cb @(posedge clk_in);
        output clock_var_output;
        input in_data;
    endclocking
    assign clk_out_port = clock_var_output; 
    assign out_data_read_input = cb.in_data;
    assign out_data_read_output_dummy = 1'b0;
    always_ff @(cb) begin
        cb.clock_var_output <= in_data;
    end
endmodule

