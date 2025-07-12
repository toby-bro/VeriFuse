module VariableLifetimes (
    input logic clk,
    output logic [7:0] out_automatic_func,
    output logic [7:0] out_automatic_proc,
    output logic out_const,
    output logic [7:0] out_static
);
    logic [7:0] module_static_var = 8'hAA;
    static logic [7:0] explicit_static_var = 8'h55;
    const  logic const_module_var = 1'b1;
    logic [7:0] func_result_reg;
    always @(posedge clk) begin
        logic [7:0] block_automatic_var;
        automatic logic [7:0] explicit_automatic_var;
        static    logic [7:0] static_in_proc_init = 8'h11;
        block_automatic_var      = module_static_var + 1;
        explicit_automatic_var   = explicit_static_var + 1;
        out_static               <= module_static_var + explicit_static_var + static_in_proc_init;
        out_automatic_proc       <= block_automatic_var + explicit_automatic_var;
        out_const                <= const_module_var;
        func_result_reg          <= call_func_wrapper(block_automatic_var);
    end
    assign out_automatic_func = func_result_reg;
    function automatic void call_func(input logic [7:0] in_arg);
        automatic logic [7:0] func_automatic_var;
        static    logic [7:0] func_static_var = 8'h33;
        func_automatic_var = in_arg + 1 + func_static_var;
    endfunction
    function automatic logic [7:0] call_func_wrapper(input logic [7:0] in_arg);
        automatic logic [7:0] func_automatic_var;
        static    logic [7:0] func_static_var_w = 8'h44;
        func_automatic_var = in_arg + 1 + func_static_var_w;
        call_func(func_automatic_var);
        return func_automatic_var;
    endfunction
endmodule

