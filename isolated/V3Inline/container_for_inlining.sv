module container_for_inlining (
    output logic [7:0] main_data_out,
    input logic main_clk,
    input logic main_reset,
    input logic [7:0] main_data_in
);
    logic [7:0] basic_comb_out;
    logic [7:0] class_module_out;
    logic hierarchy_if_out;
    logic [3:0] seq_data_out;
    logic [15:0] func_task_out;
    logic [3:0] unpacked_array_out;
    logic [7:0] public_output_wire_val;
    logic forced_output_val;
    logic simple_assign_hit_val;
    basic_comb u_basic_comb (
        .in1(main_data_in),
        .in2(main_data_in + 1),
        .out1(basic_comb_out)
    );
    (* verilator inline_module *) module_with_class u_module_with_class (
        .clk(main_clk),
        .reset(main_reset),
        .class_in(basic_comb_out),
        .class_out(class_module_out)
    );
    (* verilator inline_module *) hierarchy_if u_hierarchy_if (
        .clk(main_clk),
        .main_in(hierarchy_if_out),
        .main_out(hierarchy_if_out)
     );
    sequential_logic u_seq (
        .clk(main_clk),
        .rst_n(!main_reset),
        .data_in(main_data_in[3:0]),
        .data_out(seq_data_out)
    );
    func_task_typedef u_ft (
        .val_in({8'h00, main_data_in}),
        .enable(main_clk),
        .val_out(func_task_out)
    );
    module_with_unpacked_array u_unpacked (
        .clk(main_clk),
        .array_in_val(seq_data_out),
        .array_index(main_data_in[1:0]),
        .array_out_val(unpacked_array_out),
        .forced_input_driver(main_reset),
        .forced_output_monitor(forced_output_val),
        .public_output_wire(public_output_wire_val)
    );
    module_with_simple_assign u_simple_assign (
        .clk(main_clk),
        .reset(main_reset),
        .state_in(main_data_in[1:0]),
        .cover_hit(simple_assign_hit_val)
    );
    assign main_data_out = basic_comb_out + class_module_out + {4'h0, unpacked_array_out} + {8'h00, func_task_out[7:0]};
endmodule

