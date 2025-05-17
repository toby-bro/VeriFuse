default_nettype none;
class MyState;
    logic state;
    function new();
        state = 1'b0;
    endfunction
    function void update(logic trigger);
        if (trigger) state = ~state;
    endfunction
endclass
module mod_four_state_handling(
    input  logic [7:0] in_data,
    output logic [7:0] out_data_x,
    output logic [7:0] out_data_z,
    output logic [7:0] out_data_merged,
    output logic [7:0] out_const_x,
    output logic [7:0] out_const_z,
    output logic [7:0] out_const_xz
);
    logic [7:0] internal_x_const = 8'bx;
    logic [7:0] internal_z_const = 8'bz;
    logic [7:0] internal_xz_const = 8'b1x1z1x1z;
    assign out_data_x = internal_x_const | in_data;
    assign out_data_z = internal_z_const & in_data;
    assign out_data_merged = internal_xz_const ^ in_data;
    assign out_const_x = 8'bx;
    assign out_const_z = 8'bz;
    assign out_const_xz = 8'b1x1z1x1z;
endmodule
module mod_array_vector_selects(
    input  logic [7:0] in_unpacked_array [16],
    input  int in_array_index,
    input  logic [15:0] in_packed_vector,
    input  int in_vec_index,
    input  logic [2:0] in_slice_lsb,
    input  logic [7:0] in_lvalue_data,
    input  int in_vec_index_assign,
    input  logic in_bit_data_assign,
    output logic [7:0] out_array_read,
    output logic out_vector_read_bit,
    output logic [7:0] out_vector_slice,
    output logic [7:0] out_unpacked_array_comb_read,
    output logic out_vector_comb_bit_read,
    output logic [7:0] out_vector_comb_slice_read,
    output logic [7:0] out_array_assign_target_read,
    output logic out_vec_assign_target_read
);
    logic [7:0] unpacked_array_comb [16];
    logic [15:0] packed_vector_comb;
    logic [7:0] array_assign_target [16];
    logic [15:0] vec_assign_target;
    always_comb begin
        unpacked_array_comb = in_unpacked_array;
        packed_vector_comb = in_packed_vector;
        array_assign_target[in_array_index] = in_lvalue_data;
        vec_assign_target[in_vec_index_assign] = in_bit_data_assign;
    end
    assign out_array_read = in_unpacked_array[in_array_index];
    assign out_vector_read_bit = in_packed_vector[in_vec_index];
    assign out_vector_slice = in_packed_vector[in_slice_lsb +: 8];
    assign out_unpacked_array_comb_read = unpacked_array_comb[0];
    assign out_vector_comb_bit_read = packed_vector_comb[0];
    assign out_vector_comb_slice_read = packed_vector_comb[0 +: 8];
    assign out_array_assign_target_read = array_assign_target[0];
    assign out_vec_assign_target_read = vec_assign_target[0];
endmodule
module mod_case_comparisons(
    input  logic [3:0] in_case_val,
    input  logic [3:0] in_compare_a,
    input  logic [3:0] in_compare_b,
    output logic out_eq_case,
    output logic out_neq_case,
    output logic out_eq_wild,
    output logic out_neq_wild,
    output logic out_isunknown,
    output logic out_casez_match,
    output logic out_casex_match
);
    assign out_eq_case = (in_compare_a === in_compare_b);
    assign out_neq_case = (in_compare_a !== in_compare_b);
    assign out_eq_wild = (in_compare_a ==? in_compare_b);
    assign out_neq_wild = (in_compare_a !=? in_compare_b);
    assign out_isunknown = $isunknown(in_compare_a);
    logic [1:0] casez_out_int;
    logic [1:0] casex_out_int;
    always_comb begin
        casez_out_int = 2'b00;
        casez(in_case_val)
            4'b101z: casez_out_int = 2'b01;
            4'b11x0: casez_out_int = 2'b10;
            default: casez_out_int = 2'b11;
        endcase
        casex_out_int = 2'b00;
        casex(in_case_val)
            4'b10?1: casex_out_int = 2'b01;
            4'b?1x0: casex_out_int = 2'b10;
            default: casex_out_int = 2'b11;
        endcase
    end
    assign out_casez_match = |casez_out_int;
    assign out_casex_match = |casex_out_int;
endmodule
module mod_procedural_assignments(
    input  logic [7:0] in_pdata,
    input  logic in_clock,
    input  logic in_reset,
    output logic [7:0] out_pdata_ff,
    output logic [7:0] out_pdata_comb
);
    always @(posedge in_clock or posedge in_reset) begin
        if (in_reset) out_pdata_ff <= 8'b0;
        else out_pdata_ff <= in_pdata;
    end
    always_comb begin
        out_pdata_comb = in_pdata;
    end
endmodule
module mod_math_ops(
    input  logic [7:0] in_val_a,
    input  logic [3:0] in_val_b,
    input  logic [7:0] in_mask,
    input  logic [7:0] in_offset_data,
    input  logic [7:0] in_val_c_for_countbits,
    output logic [7:0] out_modulo,
    output logic [3:0] out_countones,
    output logic [3:0] out_countbits,
    output logic [3:0] out_countbits_no_mask,
    output logic [7:0] out_addition,
    output logic [3:0] out_countbits_constant_mask,
    output logic [3:0] out_countbits_with_x
);
    assign out_modulo = in_val_a % in_val_b;
    assign out_countones = $countones(in_val_a);
    assign out_countbits = $countbits(in_val_a, in_mask);
    assign out_countbits_no_mask = $countbits(in_val_a);
    assign out_countbits_constant_mask = $countbits(in_val_a, 8'hF0);
    assign out_countbits_with_x = $countbits(in_val_c_for_countbits, 8'b1x1z1x1z);
    assign out_addition = in_val_a + in_offset_data;
endmodule
module mod_class_instantiation(
    input  logic in_trigger,
    input  logic in_clock,
    input  logic in_enable,
    input  logic in_reset,
    output logic out_class_state,
    output logic out_class_valid
);
    MyState my_instance;
    always_comb begin
        if (my_instance == null) begin
            my_instance = new();
        end
    end
    always @(posedge in_clock or posedge in_reset) begin
        if (in_reset) begin
        end else if (in_enable) begin
            if (my_instance != null) begin
                my_instance.update(in_trigger);
            end
        end
    end
    assign out_class_state = (my_instance != null) ? my_instance.state : 1'b0;
    assign out_class_valid = (my_instance != null);
endmodule
module mod_array_index_out_of_bounds(
    input  logic [7:0] in_unpacked_array [15:0],
    input  logic [7:0] in_index_val_read,
    input  logic [7:0] in_index_val_comb_write,
    input  logic [7:0] in_data_comb_write,
    input  logic [7:0] in_index_val_seq_write,
    input  logic [7:0] in_data_seq_write,
    input  logic in_clock,
    input  logic in_reset,
    output logic [7:0] out_array_read,
    output logic [7:0] out_array_comb_write_target_read,
    output logic [7:0] out_array_seq_write_target_read
);
    logic [7:0] array_comb_write_target [15:0];
    logic [7:0] array_seq_write_target [15:0];
    always_comb begin
        array_comb_write_target[in_index_val_comb_write] = in_data_comb_write;
    end
    always @(posedge in_clock or posedge in_reset) begin
        if (in_reset) begin
        end else begin
             array_seq_write_target[in_index_val_seq_write] <= in_data_seq_write;
        end
    end
    assign out_array_read = in_unpacked_array[in_index_val_read];
    assign out_array_comb_write_target_read = array_comb_write_target[0];
    assign out_array_seq_write_target_read = array_seq_write_target[0];
endmodule
module mod_parameter_handling #(
    parameter int DATA_WIDTH = 8,
    parameter int ARRAY_SIZE = 10
)(
    input  logic [DATA_WIDTH-1:0] in_data,
    input  int in_index,
    output logic [DATA_WIDTH-1:0] out_indexed_data,
    output int out_array_size,
    output logic [DATA_WIDTH-1:0] out_param_width_var
);
    logic [DATA_WIDTH-1:0] data_array_write [ARRAY_SIZE-1:0];
    logic [DATA_WIDTH-1:0] param_width_var;
    always_comb begin
        data_array_write = '{default: '0};
        data_array_write[in_index] = in_data;
        param_width_var = in_data;
    end
    assign out_indexed_data = data_array_write[in_index % ARRAY_SIZE];
    assign out_array_size = ARRAY_SIZE;
    assign out_param_width_var = param_width_var;
endmodule
module mod_struct_select(
    input  logic [7:0] in_val_a,
    input  logic [3:0] in_val_b,
    input  logic in_flag,
    input  int in_array_index_struct,
    input  logic [7:0] in_assign_struct_a,
    input  logic in_clock,
    input  logic in_reset,
    input  logic [7:0] in_assign_struct_a_seq,
    input  int in_array_index_struct_seq,
    output logic [7:0] out_struct_a_read,
    output logic [3:0] out_struct_b_read,
    output logic out_struct_flag_read,
    output logic [7:0] out_struct_array_comb_assign_target_read,
    output logic [7:0] out_struct_array_seq_assign_target_read
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [3:0] field_b;
        logic       field_flag;
    } my_struct_t;
    my_struct_t my_struct_var;
    my_struct_t my_struct_array [16];
    my_struct_t my_struct_array_comb_assign_target [16];
    my_struct_t my_struct_array_seq_assign_target [16];
    always_comb begin
        my_struct_var.field_a = in_val_a;
        my_struct_var.field_b = in_val_b;
        my_struct_var.field_flag = in_flag;
        my_struct_array_comb_assign_target[in_array_index_struct].field_a = in_assign_struct_a;
    end
    always @(posedge in_clock or posedge in_reset) begin
         if (in_reset) begin
         end else begin
            my_struct_array_seq_assign_target[in_array_index_struct_seq].field_a <= in_assign_struct_a_seq;
         end
    end
    assign out_struct_a_read = my_struct_var.field_a;
    assign out_struct_b_read = my_struct_var.field_b;
    assign out_struct_flag_read = my_struct_var.field_flag;
    assign out_struct_array_comb_assign_target_read = my_struct_array_comb_assign_target[0].field_a;
    assign out_struct_array_seq_assign_target_read = my_struct_array_seq_assign_target[0].field_a;
endmodule
module mod_tristate_handling(
    input  logic in_data,
    input  logic in_en,
    output logic out_data
);
    assign (strong1, weak0) out_data = in_en ? in_data : 1'bz;
endmodule
