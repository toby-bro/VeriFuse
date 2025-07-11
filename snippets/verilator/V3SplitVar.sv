module module_unpacked_array (
    input logic in1,
    input logic in2,
    output logic out1,
    output logic out2
);
    logic [1:0] data_ua[0:1] /*verilator split_var*/;
    always_comb begin
        data_ua[0][0] = in1;
        data_ua[0][1] = in2;
        data_ua[1][0] = data_ua[0][0];
        data_ua[1][1] = ~data_ua[0][1];
    end
    assign out1 = data_ua[1][0];
    assign out2 = data_ua[1][1];
endmodule
module module_packed_variables (
    input logic [7:0] data_in_pv,
    input logic [15:0] data_in_pa,
    input logic enable_pv,
    output logic [3:0] data_out_pv,
    output logic [7:0] data_out_pa
);
    logic [31:0] data_pv /*verilator split_var*/;
    logic [7:0] data_pa[0:1] /*verilator split_var*/;
    always_comb begin
        if (enable_pv) begin
            data_pv[7:0] = data_in_pv;
            data_pv[15:8] = ~data_in_pv;
            data_pv[23:16] = data_pv[7:0];
            data_pv[31:24] = data_pv[15:8];
            data_pa[0] = data_in_pa[7:0];
            data_pa[1] = data_in_pa[15:8];
        end else begin
            data_pv = 32'h0;
            data_pa[0] = 8'h0;
            data_pa[1] = 8'h0;
        end
    end
    assign data_out_pv = data_pv[3:0];
    assign data_out_pa = data_pa[0];
endmodule
module module_structs (
    input logic enable_init,
    output logic init_done_ps,
    output logic init_done_us,
    output logic [7:0] us_var_out
);
    typedef struct packed {
        logic field_a;
        logic [3:0] field_b;
    } packed_struct_t;
    typedef struct {
        logic field_c;
        logic [7:0] field_d;
    } unpacked_struct_t;
    packed_struct_t ps_var /*verilator split_var*/;
    unpacked_struct_t us_var[0:1];
    logic local_init_done_ps;
    logic local_init_done_us;
    always_comb begin
        if (enable_init) begin
            ps_var.field_a = 1'b0;
            ps_var.field_b = 4'b1010;
            us_var[0].field_c = 1'b1;
            us_var[0].field_d = 8'hAA;
            us_var[1] = us_var[0];
            us_var[1].field_c = us_var[0].field_c;
            local_init_done_ps = 1'b1;
            local_init_done_us = 1'b1;
        end else begin
            ps_var = {1'b1, 4'b0101};
            us_var[0].field_c = 1'b0;
            us_var[0].field_d = 8'h00;
            us_var[1].field_c = 1'b0;
            us_var[1].field_d = 8'h00;
            local_init_done_ps = 1'b0;
            local_init_done_us = 1'b0;
        end
    end
    assign init_done_ps = local_init_done_ps;
    assign init_done_us = local_init_done_us;
    assign us_var_out = us_var[0].field_d;
endmodule
module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a /*verilator split_var*/;
    logic [7:0] data_b /*verilator split_var*/;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local /*verilator split_var*/;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule
module module_constrained_var (
    input logic [3:0] input_cv,
    output logic [3:0] output_cv,
    inout wire [3:0] inout_cv,
    input logic enable_cv,
    output logic [7:0] counter_cv_out,
    output logic [7:0] counter_split_out
);
    logic [7:0] internal_state /*verilator public*/;
    logic [15:0] forceable_var /*verilator forceable*/;
    logic [7:0] counter_cv;
    logic [7:0] counter_split /*verilator split_var*/;
    assign output_cv = input_cv;
    assign inout_cv = input_cv;
    assign counter_cv_out = counter_cv;
    assign counter_split_out = counter_split;
    always_comb begin
        if (enable_cv) begin
            counter_cv = counter_cv + 8'b1;
            internal_state = counter_cv;
            forceable_var = {counter_cv, counter_cv};
        end else begin
            counter_cv = 8'b0;
            internal_state = 8'h00;
            forceable_var = 16'h0000;
        end
        counter_split = counter_cv + 8'd10;
    end
endmodule
module module_packed_logic (
    input logic [9:0] data_in_pl,
    input logic data_in_in_pl,
    output logic [4:0] data_out_pl
);
    logic [15:0] my_packed_logic /*verilator split_var*/;
    always_comb begin
        my_packed_logic[9:0] = data_in_pl;
        my_packed_logic[15:10] = 6'h3F;
        my_packed_logic[0] = data_in_in_pl;
    end
    assign data_out_pl[4:1] = my_packed_logic[4:1];
    assign data_out_pl[0] = my_packed_logic[1];
endmodule
module module_ast_sel (
    input logic [31:0] raw_data_as,
    input logic [7:0] input_byte_as,
    output logic [7:0] extracted_byte_as,
    output logic [7:0] another_byte_out
);
    logic [31:0] packed_data_as /*verilator split_var*/;
    assign packed_data_as = raw_data_as;
    assign extracted_byte_as = packed_data_as[15:8];
    logic [7:0] another_byte_as;
    assign another_byte_as = packed_data_as[7:0];
    assign packed_data_as[23:16] = input_byte_as;
    assign another_byte_out = another_byte_as;
endmodule
module module_unpacked_packed_struct_array (
    input logic [3:0] enable_elements_upsa,
    input logic trigger_upsa,
    output logic [3:0] status_flags_upsa
);
    typedef struct packed {
        logic flag;
        logic [2:0] value;
    } packed_element_t;
    packed_element_t elements_upsa[0:3] /*verilator split_var*/;
    logic [3:0] temp_flags_upsa;
    always_comb begin
        if (trigger_upsa) begin
            if (enable_elements_upsa[0]) begin
                elements_upsa[0].flag = 1'b1;
                elements_upsa[0].value = 3'b000;
            end else begin
                elements_upsa[0].flag = 1'b0;
                elements_upsa[0].value = 3'b000;
            end
            if (enable_elements_upsa[1]) begin
                elements_upsa[1].flag = 1'b1;
                elements_upsa[1].value = 3'b001;
            end else begin
                elements_upsa[1].flag = 1'b0;
                elements_upsa[1].value = 3'b000;
            end
            if (enable_elements_upsa[2]) begin
                elements_upsa[2].flag = 1'b1;
                elements_upsa[2].value = 3'b010;
            end else begin
                elements_upsa[2].flag = 1'b0;
                elements_upsa[2].value = 3'b000;
            end
            if (enable_elements_upsa[3]) begin
                elements_upsa[3].flag = 1'b1;
                elements_upsa[3].value = 3'b011;
            end else begin
                elements_upsa[3].flag = 1'b0;
                elements_upsa[3].value = 3'b000;
            end
        end else begin
            elements_upsa[0].flag = 1'b0;
            elements_upsa[0].value = 3'b0;
            elements_upsa[1].flag = 1'b0;
            elements_upsa[1].value = 3'b0;
            elements_upsa[2].flag = 1'b0;
            elements_upsa[2].value = 3'b0;
            elements_upsa[3].flag = 1'b0;
            elements_upsa[3].value = 3'b0;
        end
        temp_flags_upsa[0] = elements_upsa[0].flag;
        temp_flags_upsa[1] = elements_upsa[1].flag;
        temp_flags_upsa[2] = elements_upsa[2].flag;
        temp_flags_upsa[3] = elements_upsa[3].flag;
    end
    assign status_flags_upsa = temp_flags_upsa;
endmodule
module module_packed_array (
    input logic [31:0] input_pa,
    input logic enable_pa,
    input logic [3:0] input_slice_pa,
    output logic [7:0] output_pa,
    output logic [7:0] output_pa_element1
);
    logic [7:0] my_packed_array[0:3] /*verilator split_var*/;
    always_comb begin
        if (enable_pa) begin
            my_packed_array[0] = input_pa[7:0];
            my_packed_array[1] = input_pa[15:8];
            my_packed_array[2] = input_pa[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = input_slice_pa;
    end
    assign output_pa = my_packed_array[3];
    assign output_pa_element1 = my_packed_array[1];
endmodule
module module_bitfield_concat (
    input logic [7:0] input_bf,
    input logic [3:0] input_bf_slice,
    output logic [7:0] output_bf,
    output logic [3:0] output_bf_slice
);
    logic [7:0] my_bitfield /*verilator split_var*/;
    always_comb begin
        if (input_bf[7]) begin
            my_bitfield = input_bf;
        end else begin
            my_bitfield = {input_bf[0], input_bf[7:1]};
        end
        my_bitfield[3:0] = input_bf_slice;
    end
    assign output_bf = my_bitfield;
    assign output_bf_slice = my_bitfield[3:0];
endmodule
module module_sensitivity_list (
    input logic clock_sl,
    input logic data_in_sl,
    input logic enable_sl,
    output logic state_out_sl,
    output logic data_split_out_sl
);
    logic state_sl;
    logic [1:0] data_split_sl /*verilator split_var*/;
    always_comb begin
        @(data_in_sl or enable_sl or data_split_sl)
        state_sl = enable_sl ^ data_in_sl ^ data_split_sl[0];
    end
    always_comb begin
        data_split_sl[0] = data_in_sl & enable_sl;
        data_split_sl[1] = data_in_sl | enable_sl;
    end
    assign state_out_sl = state_sl;
    assign data_split_out_sl = data_split_sl[0];
endmodule
