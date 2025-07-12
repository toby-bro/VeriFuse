module MiscExpressions_AssignmentErrors (
    input logic clk_err,
    input bit in_auto_bit_input,
    input bit in_bit_input,
    input int in_int_input,
    output logic out_nonblocking_dummy,
    output logic out_placeholder
);
    logic net_var; 
    int var_assignable; 
    const int const_var = 5;
    always_comb begin
        net_var = in_bit_input; 
        var_assignable = in_int_input; 
    end
    always @(posedge clk_err) begin
        automatic bit auto_var; 
        auto_var = in_auto_bit_input; 
    end
    assign out_placeholder = 1'b1;
    assign out_nonblocking_dummy = 1'b0;
endmodule

