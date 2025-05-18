module basic_comb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1
);
    (* verilator inline_module *) ;
    logic [7:0] temp_wire;
    assign temp_wire = in1 + in2;
    always_comb begin
        out1 = temp_wire;
    end
endmodule
module sequential_logic (
    input logic clk,
    input logic rst_n,
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    (* verilator no_inline_module *) ;
    logic [3:0] internal_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 4'h0;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule
module func_task_typedef (
    input logic [15:0] val_in,
    input logic enable,
    output logic [15:0] val_out
);
    typedef logic [15:0] my_data_t;
    my_data_t temp_val;
    function automatic my_data_t add_one(my_data_t input_val);
        return input_val + 1;
    endfunction
    task automatic set_value(my_data_t set_val);
        temp_val = set_val;
    endtask
    always_comb begin
        if (enable) begin
            set_value(add_one(val_in));
        end else begin
            set_value(val_in);
        end
        val_out = temp_val;
    end
endmodule
module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule
interface simple_if (input logic clk);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module hierarchy_if (
    input logic clk,
    input logic main_in,
    output logic main_out
);
    sub_module u_sub (
        .sub_in(main_in),
        .sub_out(main_out)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = main_in;
        if_inst.ready = main_out;
    end
endmodule
class SimpleClass;
    logic [7:0] internal_data;
    function new();
        internal_data = 8'h0;
    endfunction
    function void set_data(logic [7:0] val);
        internal_data = val;
    endfunction
    function logic [7:0] get_data();
        return internal_data;
    endfunction
endclass
module module_with_class (
    input logic clk,
    input logic reset,
    input logic [7:0] class_in,
    output logic [7:0] class_out
);
    SimpleClass my_object;
    logic [7:0] stored_data;
    initial begin
        my_object = new();
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stored_data <= 8'h0;
        end else begin
            my_object.set_data(class_in);
            stored_data <= my_object.get_data();
        end
    end
    assign class_out = stored_data;
endmodule
module module_with_unpacked_array (
    input logic clk,
    input logic [3:0] array_in_val,
    input logic [1:0] array_index,
    output logic [3:0] array_out_val,
    input logic forced_input_driver,
    output logic forced_output_monitor,
    (* verilator public *) output logic [7:0] public_output_wire
);
    logic [3:0] unpacked_reg_array [0:3];
    (* verilator public *) logic [3:0] public_unpacked_array [0:1];
    (* wire_force_assign *) logic forced_internal_in;
    (* wire_force_release *) logic forced_internal_out;
    always_ff @(posedge clk) begin
        unpacked_reg_array[array_index] <= array_in_val;
        public_unpacked_array[0] <= array_in_val;
        public_unpacked_array[1] <= array_out_val;
    end
    assign array_out_val = unpacked_reg_array[array_index];
    assign public_output_wire = public_unpacked_array[0] + public_unpacked_array[1];
    logic local_clk_ref;
    assign local_clk_ref = clk;
    assign forced_internal_in = forced_input_driver;
    assign forced_output_monitor = forced_internal_out;
endmodule
module module_with_simple_assign (
    input logic clk,
    input logic reset,
    input logic [1:0] state_in,
    output logic cover_hit
);
    logic [1:0] current_state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= 2'b00;
        end else begin
            current_state <= state_in;
        end
    end
    assign cover_hit = (current_state inside {2'b00, 2'b11});
endmodule
module container_for_inlining (
    input logic main_clk,
    input logic main_reset,
    input logic [7:0] main_data_in,
    output logic [7:0] main_data_out
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
