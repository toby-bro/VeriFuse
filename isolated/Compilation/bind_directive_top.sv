module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module bind_directive_top (
    input logic i_clk,
    input logic [3:0] i_control,
    input logic [7:0] i_data,
    output logic [7:0] o_result,
    output logic o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule

