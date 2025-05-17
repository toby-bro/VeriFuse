typedef struct packed {
    logic [7:0] f1;
    logic [15:0] f2;
    logic [31:0] f3;
} packed_struct_t;
typedef struct packed {
    logic [7:0] f1;
    logic [15:0] f2;
    logic [31:0] f3;
    string s1;
} packed_struct_with_string_t;
typedef struct {
    logic [7:0] uf1;
    logic [15:0] uf2;
    logic [31:0] uf3;
} unpacked_struct_t;
typedef struct {
    logic scalar_field;
    logic [7:0] vector_field;
} mixed_struct_t;
module PackedArraySel_Desc #(
    parameter int P_BIT_INDEX = 6,
    parameter int P_MSB_RANGE = 7,
    parameter int P_LSB_RANGE = 4,
    parameter int P_PLUS_START = 5,
    parameter int P_PLUS_WIDTH = 3,
    parameter int P_MINUS_START = 7,
    parameter int P_MINUS_WIDTH = 3
) (
    input logic [2:0] index_bit,
    input logic [7:4] data_element_0,
    input logic [7:4] data_element_1,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    logic [7:4] packed_arr [0:1];
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        packed_arr[0] = data_element_0;
        packed_arr[1] = data_element_1;
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit)) bit_out_var_index = packed_arr[0][index_bit];
        bit_out_param_index = packed_arr[0][P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = packed_arr[0][P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = packed_arr[0][P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = packed_arr[0][P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = packed_arr[0][P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module PackedArraySel_Asc #(
    parameter int P_BIT_INDEX = 2,
    parameter int P_MSB_RANGE = 4,
    parameter int P_LSB_RANGE = 1,
    parameter int P_PLUS_START = 1,
    parameter int P_PLUS_WIDTH = 4,
    parameter int P_MINUS_START = 6,
    parameter int P_MINUS_WIDTH = 4
) (
    input logic [2:0] index_bit,
    input logic [0:7] data_element_0,
    input logic [0:7] data_element_1,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    logic [0:7] packed_arr [0:1];
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        packed_arr[0] = data_element_0;
        packed_arr[1] = data_element_1;
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit)) bit_out_var_index = packed_arr[0][index_bit];
        bit_out_param_index = packed_arr[0][P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = packed_arr[0][P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = packed_arr[0][P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = packed_arr[0][P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = packed_arr[0][P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module UnpackedArraySel #(
    parameter int P_SLICE_HI = 2,
    parameter int P_SLICE_LO = 1,
    parameter int P_PLUS_START = 1,
    parameter int P_PLUS_WIDTH = 2,
    parameter int P_MINUS_START = 2,
    parameter int P_MINUS_WIDTH = 2
) (
    input logic [1:0] index_bit,
    input logic [7:0] data_in [0:3],
    output logic [7:0] elem_out_selbit,
    output int slice_msb_lsb_size,
    output logic [7:0] first_elem_msb_lsb,
    output int slice_plus_size,
    output logic [7:0] first_elem_plus,
    output int slice_minus_size,
    output logic [7:0] first_elem_minus
);
    logic [7:0] unpacked_arr [0:3];
    localparam int ARR_SIZE = unpacked_arr.size();
    logic [7:0] sliced_msb_lsb [];
    logic [7:0] sliced_plus [];
    logic [7:0] sliced_minus [];
    always_comb begin
        unpacked_arr = data_in;
        elem_out_selbit = 8'hXX;
        slice_msb_lsb_size = 0;
        first_elem_msb_lsb = 8'hXX;
        slice_plus_size = 0;
        first_elem_plus = 8'hXX;
        slice_minus_size = 0;
        first_elem_minus = 8'hXX;
        if ($isknown(index_bit) && index_bit >= 0 && index_bit < ARR_SIZE) elem_out_selbit = unpacked_arr[index_bit];
        if ((P_SLICE_HI >= 0 && P_SLICE_HI < ARR_SIZE) && (P_SLICE_LO >= 0 && P_SLICE_LO < ARR_SIZE)) begin
            if (P_SLICE_HI >= P_SLICE_LO) sliced_msb_lsb = unpacked_arr[P_SLICE_HI:P_SLICE_LO];
            else sliced_msb_lsb = unpacked_arr[P_SLICE_LO:P_SLICE_HI];
        end else begin
             sliced_msb_lsb = {};
        end
        slice_msb_lsb_size = sliced_msb_lsb.size();
        if (slice_msb_lsb_size > 0) first_elem_msb_lsb = sliced_msb_lsb[0];
        if (P_PLUS_WIDTH > 0 && (P_PLUS_START >= 0 && P_PLUS_START + P_PLUS_WIDTH - 1 < ARR_SIZE)) begin
             sliced_plus = unpacked_arr[P_PLUS_START +: P_PLUS_WIDTH];
        end else begin
             sliced_plus = {};
        end
        slice_plus_size = sliced_plus.size();
        if (slice_plus_size > 0) first_elem_plus = sliced_plus[0];
        if (P_MINUS_WIDTH > 0 && (P_MINUS_START >= 0 && P_MINUS_START - P_MINUS_WIDTH + 1 >= 0)) begin
            sliced_minus = unpacked_arr[P_MINUS_START -: P_MINUS_WIDTH];
        end else begin
             sliced_minus = {};
        end
        slice_minus_size = sliced_minus.size();
        if (slice_minus_size > 0) first_elem_minus = sliced_minus[0];
    end
endmodule
module VectorSel_Desc #(
    parameter int P_BIT_INDEX = 10,
    parameter int P_MSB_RANGE = 15,
    parameter int P_LSB_RANGE = 8,
    parameter int P_PLUS_START = 9,
    parameter int P_PLUS_WIDTH = 4,
    parameter int P_MINUS_START = 15,
    parameter int P_MINUS_WIDTH = 4
) (
    input logic [3:0] index_bit,
    input logic [15:8] vec_in,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    logic [15:8] vec_desc = vec_in;
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit)) bit_out_var_index = vec_desc[index_bit];
        bit_out_param_index = vec_desc[P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = vec_desc[P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = vec_desc[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = vec_desc[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = vec_desc[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module VectorSel_Asc #(
    parameter int P_BIT_INDEX = 5,
    parameter int P_MSB_RANGE = 10,
    parameter int P_LSB_RANGE = 3,
    parameter int P_PLUS_START = 4,
    parameter int P_PLUS_WIDTH = 8,
    parameter int P_MINUS_START = 11,
    parameter int P_MINUS_WIDTH = 8
) (
    input logic [3:0] index_bit,
    input logic [0:15] vec_in,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    logic [0:15] vec_asc = vec_in;
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit)) bit_out_var_index = vec_asc[index_bit];
        bit_out_param_index = vec_asc[P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = vec_asc[P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = vec_asc[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = vec_asc[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = vec_asc[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module VectorSel_Asc_NegLSB #(
    parameter int P_BIT_INDEX = -5,
    parameter int P_MSB_RANGE = 0,
    parameter int P_LSB_RANGE = -7,
    parameter int P_PLUS_START = -4,
    parameter int P_PLUS_WIDTH = 8,
    parameter int P_MINUS_START = -11,
    parameter int P_MINUS_WIDTH = 8
) (
    input int index_bit,
    input logic [0:-15] vec_in,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    logic [0:-15] vec_asc_neglsb = vec_in;
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit)) bit_out_var_index = vec_asc_neglsb[index_bit];
        bit_out_param_index = vec_asc_neglsb[P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = vec_asc_neglsb[P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = vec_asc_neglsb[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = vec_asc_neglsb[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = vec_asc_neglsb[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module AssocArraySel (
    input int index_key,
    input logic [7:0] data_in_default,
    output logic [7:0] data_out_sel,
    output logic exists_out
);
    logic [7:0] assoc_arr [int];
    always_comb begin
        assoc_arr[10] = data_in_default;
        exists_out = assoc_arr.exists(index_key);
        data_out_sel = 8'hXX;
        if (exists_out) begin
             data_out_sel = assoc_arr[index_key];
        end
    end
endmodule
module WildcardArraySel (
    input int index_key,
    input logic [7:0] data_in_default,
    output logic [7:0] data_out_sel
);
    logic [7:0] wildcard_arr [*];
    always_comb begin
        wildcard_arr[5] = data_in_default;
        data_out_sel = wildcard_arr[index_key];
        if ($isunknown(data_out_sel)) data_out_sel = 8'hYY;
    end
endmodule
module DynArraySel (
    input int index,
    input logic [7:0] data_in_arr [],
    output logic [7:0] data_out_sel,
    output int array_size
);
    logic [7:0] dyn_arr [];
    always_comb begin
        dyn_arr = data_in_arr;
        array_size = dyn_arr.size();
        data_out_sel = 8'hXX;
        if (index >= 0 && index < dyn_arr.size()) begin
            data_out_sel = dyn_arr[index];
        end
    end
endmodule
module QueueSel (
    input int index_front,
    input int index_back,
    input logic [7:0] data_in_q [$],
    output logic [7:0] data_out_front,
    output logic [7:0] data_out_back
);
    logic [7:0] queue_q [$];
    always_comb begin
        queue_q = data_in_q;
        data_out_front = 8'hXX;
        data_out_back = 8'hXX;
        if (index_front >= 0 && index_front < queue_q.size()) begin
            data_out_front = queue_q[index_front];
        end
        if ($abs(index_back) < queue_q.size() && index_back <= 0) begin
             data_out_back = queue_q[$+index_back];
        end
    end
endmodule
module QueueSliceSel #(
    parameter int P_SLICE_HI = 4,
    parameter int P_SLICE_LO = 1,
    parameter int P_FB_END_OFFSET = 2,
    parameter int P_BB_HI_OFFSET = 3,
    parameter int P_BB_LO_OFFSET = 0
) (
    input logic [7:0] data_in_q [$],
    output int slice_msb_lsb_size,
    output logic [7:0] first_elem_msb_lsb,
    output int slice_front_back_size,
    output logic [7:0] first_elem_front_back,
    output int slice_back_back_size,
    output logic [7:0] first_elem_back_back
);
    logic [7:0] queue_q [$];
    logic [7:0] sliced_msb_lsb [$];
    logic [7:0] sliced_front_back [$];
    logic [7:0] sliced_back_back [$];
    always_comb begin
        queue_q = data_in_q;
        if (queue_q.size() > 0 && P_SLICE_HI >= 0 && P_SLICE_LO >= 0 && P_SLICE_HI < queue_q.size() && P_SLICE_LO < queue_q.size()) begin
             sliced_msb_lsb = queue_q[P_SLICE_HI:P_SLICE_LO];
        end else begin
             sliced_msb_lsb = {};
        end
        slice_msb_lsb_size = sliced_msb_lsb.size();
        first_elem_msb_lsb = (slice_msb_lsb_size > 0) ? sliced_msb_lsb[0] : 8'hXX;
        if (queue_q.size() > 0 && P_FB_END_OFFSET >= 0 && P_FB_END_OFFSET <= queue_q.size()) begin
             sliced_front_back = queue_q[0:$-P_FB_END_OFFSET];
        end else begin
             sliced_front_back = {};
        end
        slice_front_back_size = sliced_front_back.size();
        first_elem_front_back = (slice_front_back_size > 0) ? sliced_front_back[0] : 8'hXX;
        if (queue_q.size() > 0 && P_BB_HI_OFFSET >= 0 && P_BB_HI_OFFSET <= queue_q.size() && P_BB_LO_OFFSET >= 0 && P_BB_LO_OFFSET <= queue_q.size()) begin
             sliced_back_back = queue_q[$-P_BB_HI_OFFSET:$-P_BB_LO_OFFSET];
        end else begin
             sliced_back_back = {};
        end
        slice_back_back_size = sliced_back_back.size();
        first_elem_back_back = (slice_back_back_size > 0) ? sliced_back_back[0] : 8'hXX;
    end
endmodule
module StringSel (
    input int index,
    input string data_in,
    output logic [7:0] char_out
);
    string my_string = data_in;
    always_comb begin
        char_out = 8'h00;
        if (index >= 0 && index < my_string.len())
             char_out = my_string[index];
    end
endmodule
module WritableStringSel (
    input int index,
    input logic [7:0] char_in,
    input string string_in,
    output logic success,
    output string string_out
);
    string my_writable_string;
    always_comb begin
        my_writable_string = string_in;
        success = 1'b0;
        if (index >= 0 && index < my_writable_string.len()) begin
             my_writable_string[index] = char_in;
             success = 1'b1;
        end
        string_out = my_writable_string;
    end
endmodule
module PackedStructMemberSel #(
    parameter int P_F1_BIT_INDEX = 2,
    parameter int P_F2_BIT_INDEX = 5,
    parameter int P_F2_SLICE_HI = 10,
    parameter int P_F2_SLICE_LO = 3,
    parameter int P_F2_PLUS_START = 4,
    parameter int P_F2_PLUS_WIDTH = 8,
    parameter int P_F2_MINUS_START = 11,
    parameter int P_F2_MINUS_WIDTH = 8,
    parameter int P_S1_BIT_INDEX = 3
) (
    input logic [2:0] index_f1_bit_var,
    input logic [3:0] index_f2_bit_var,
    input int index_s1_bit_var,
    input packed_struct_with_string_t ps_in,
    output logic bit_out_f1_var_index,
    output logic bit_out_f1_param_index,
    output logic bit_out_f2_var_index,
    output logic bit_out_f2_param_index,
    output logic [($abs(P_F2_SLICE_HI - P_F2_SLICE_LO)) : 0] range_out_msb_lsb_f2,
    output logic [(P_F2_PLUS_WIDTH - 1) : 0] range_out_plus_f2,
    output logic [(P_F2_MINUS_WIDTH - 1) : 0] range_out_minus_f2,
    output logic [7:0] char_out_s1_var_index,
    output logic [7:0] char_out_s1_param_index
);
    packed_struct_with_string_t ps = ps_in;
    localparam int F2_MSBLSB_WIDTH = $abs(P_F2_SLICE_HI - P_F2_SLICE_LO) + 1;
    localparam int F2_PLUS_WIDTH = P_F2_PLUS_WIDTH;
    localparam int F2_MINUS_WIDTH = P_F2_MINUS_WIDTH;
    always_comb begin
        bit_out_f1_var_index = 1'bX;
        bit_out_f1_param_index = 1'bX;
        bit_out_f2_var_index = 1'bX;
        bit_out_f2_param_index = 1'bX;
        range_out_msb_lsb_f2 = {F2_MSBLSB_WIDTH {'X'}};
        range_out_plus_f2 = {F2_PLUS_WIDTH {'X'}};
        range_out_minus_f2 = {F2_MINUS_WIDTH {'X'}};
        char_out_s1_var_index = 8'h00;
        char_out_s1_param_index = 8'h00;
        if ($isknown(index_f1_bit_var)) bit_out_f1_var_index = ps.f1[index_f1_bit_var];
        bit_out_f1_param_index = ps.f1[P_F1_BIT_INDEX];
        if ($isknown(index_f2_bit_var)) bit_out_f2_var_index = ps.f2[index_f2_bit_var];
        bit_out_f2_param_index = ps.f2[P_F2_BIT_INDEX];
        if (P_F2_SLICE_HI >= P_F2_SLICE_LO) range_out_msb_lsb_f2 = ps.f2[P_F2_SLICE_HI:P_F2_SLICE_LO];
        else range_out_msb_lsb_f2 = ps.f2[P_F2_SLICE_LO:P_F2_SLICE_HI];
        range_out_plus_f2 = ps.f2[P_F2_PLUS_START +: P_F2_PLUS_WIDTH];
        range_out_minus_f2 = ps.f2[P_F2_MINUS_START -: P_F2_MINUS_WIDTH];
        if (index_s1_bit_var >= 0 && index_s1_bit_var < ps.s1.len())
            char_out_s1_var_index = ps.s1[index_s1_bit_var];
        if (P_S1_BIT_INDEX >= 0 && P_S1_BIT_INDEX < ps.s1.len())
            char_out_s1_param_index = ps.s1[P_S1_BIT_INDEX];
    end
endmodule
module PackedStructDirectSel #(
    parameter int P_BIT_INDEX = 20,
    parameter int P_MSB_RANGE = 40,
    parameter int P_LSB_RANGE = 25,
    parameter int P_PLUS_START = 30,
    parameter int P_PLUS_WIDTH = 16,
    parameter int P_MINUS_START = 45,
    parameter int P_MINUS_WIDTH = 16
) (
    input logic [5:0] index_bit_var,
    input packed_struct_t ps_direct_in,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    packed_struct_t ps_direct = ps_direct_in;
    localparam int TOTAL_BITS = $bits(packed_struct_t);
    localparam int MSBLSB_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        bit_out_var_index = 1'bX;
        bit_out_param_index = 1'bX;
        range_out_msb_lsb = {MSBLSB_WIDTH {'X'}};
        range_out_plus = {PLUS_WIDTH {'X'}};
        range_out_minus = {MINUS_WIDTH {'X'}};
        if ($isknown(index_bit_var)) bit_out_var_index = ps_direct[index_bit_var];
        bit_out_param_index = ps_direct[P_BIT_INDEX];
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out_msb_lsb = ps_direct[P_MSB_RANGE:P_LSB_RANGE];
        else range_out_msb_lsb = ps_direct[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = ps_direct[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = ps_direct[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module UnpackedStructMemberSel #(
    parameter int P_F1_BIT_INDEX = 2,
    parameter int P_F2_BIT_INDEX = 5,
    parameter int P_F2_SLICE_HI = 10,
    parameter int P_F2_SLICE_LO = 3,
    parameter int P_F2_PLUS_START = 4,
    parameter int P_F2_PLUS_WIDTH = 8,
    parameter int P_F2_MINUS_START = 11,
    parameter int P_F2_MINUS_WIDTH = 8
) (
    input logic [2:0] index_f1_bit_var,
    input logic [3:0] index_f2_bit_var,
    input unpacked_struct_t us_in,
    output logic bit_out_f1_var_index,
    output logic bit_out_f1_param_index,
    output logic bit_out_f2_var_index,
    output logic bit_out_f2_param_index,
    output logic [($abs(P_F2_SLICE_HI - P_F2_SLICE_LO)) : 0] range_out_msb_lsb_f2,
    output logic [(P_F2_PLUS_WIDTH - 1) : 0] range_out_plus_f2,
    output logic [(P_F2_MINUS_WIDTH - 1) : 0] range_out_minus_f2,
    output logic [31:0] dummy_uf3_out
);
    unpacked_struct_t us = us_in;
    localparam int F2_MSBLSB_WIDTH = $abs(P_F2_SLICE_HI - P_F2_SLICE_LO) + 1;
    localparam int F2_PLUS_WIDTH = P_F2_PLUS_WIDTH;
    localparam int F2_MINUS_WIDTH = P_F2_MINUS_WIDTH;
    always_comb begin
        bit_out_f1_var_index = 1'bX;
        bit_out_f1_param_index = 1'bX;
        bit_out_f2_var_index = 1'bX;
        bit_out_f2_param_index = 1'bX;
        range_out_msb_lsb_f2 = {F2_MSBLSB_WIDTH {'X'}};
        range_out_plus_f2 = {F2_PLUS_WIDTH {'X'}};
        range_out_minus_f2 = {F2_MINUS_WIDTH {'X'}};
        dummy_uf3_out = us.uf3;
        if ($isknown(index_f1_bit_var)) bit_out_f1_var_index = us.uf1[index_f1_bit_var];
        bit_out_f1_param_index = us.uf1[P_F1_BIT_INDEX];
        if ($isknown(index_f2_bit_var)) bit_out_f2_var_index = us.uf2[index_f2_bit_var];
        bit_out_f2_param_index = us.uf2[P_F2_BIT_INDEX];
        if (P_F2_SLICE_HI >= P_F2_SLICE_LO) range_out_msb_lsb_f2 = us.uf2[P_F2_SLICE_HI:P_F2_SLICE_LO];
        else range_out_msb_lsb_f2 = us.uf2[P_F2_SLICE_LO:P_F2_SLICE_HI];
        range_out_plus_f2 = us.uf2[P_F2_PLUS_START +: P_F2_PLUS_WIDTH];
        range_out_minus_f2 = us.uf2[P_F2_MINUS_START -: P_F2_MINUS_WIDTH];
    end
endmodule
module ConstantSel #(
    parameter int P_BIT_INDEX = 2,
    parameter int P_RANGE_HI = 7,
    parameter int P_LSB_RANGE = 4,
    parameter int P_PLUS_START = 1,
    parameter int P_PLUS_WIDTH = 3,
    parameter int P_MINUS_START = 6,
    parameter int P_MINUS_WIDTH = 3
) (
    input logic dummy_in,
    output logic bit_out,
    output logic [($abs(P_RANGE_HI - P_LSB_RANGE)) : 0] range_out,
    output logic [(P_PLUS_WIDTH - 1) : 0] plus_out,
    output logic [(P_MINUS_WIDTH - 1) : 0] minus_out
);
    localparam logic [7:0] CONST_VAL = 8'hA5;
    localparam int RANGE_WIDTH = $abs(P_RANGE_HI - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
        bit_out = 1'bX;
        range_out = {RANGE_WIDTH {'X'}};
        plus_out = {PLUS_WIDTH {'X'}};
        minus_out = {MINUS_WIDTH {'X'}};
        bit_out = CONST_VAL[P_BIT_INDEX];
        if (P_RANGE_HI >= P_LSB_RANGE) range_out = CONST_VAL[P_RANGE_HI:P_LSB_RANGE];
        else range_out = CONST_VAL[P_LSB_RANGE:P_RANGE_HI];
        plus_out = CONST_VAL[P_PLUS_START +: P_PLUS_WIDTH];
        minus_out = CONST_VAL[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module StringLiteralSel (
    input int index,
    input logic dummy_in,
    output logic [7:0] char_out
);
    string my_string_literal = "literal_string";
    always_comb begin
        char_out = 8'h00;
        if (index >= 0 && index < my_string_literal.len())
             char_out = my_string_literal[index];
    end
endmodule
module ParameterSel #(
    parameter logic [15:0] P_CONST_VAL = 16'h1234,
    parameter int P_BIT_INDEX = 5,
    parameter int P_RANGE_HI = 15,
    parameter int P_LSB_RANGE = 8,
    parameter int P_PLUS_START = 4,
    parameter int P_PLUS_WIDTH = 8,
    parameter int P_MINUS_START = 11,
    parameter int P_MINUS_WIDTH = 8
) (
    input logic [3:0] index_bit_var,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_RANGE_HI - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    localparam int RANGE_WIDTH = $abs(P_RANGE_HI - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
         bit_out_var_index = 1'bX;
         bit_out_param_index = 1'bX;
         range_out_msb_lsb = {RANGE_WIDTH {'X'}};
         range_out_plus = {PLUS_WIDTH {'X'}};
         range_out_minus = {MINUS_WIDTH {'X'}};
         if ($isknown(index_bit_var))
             bit_out_var_index = P_CONST_VAL[index_bit_var];
        bit_out_param_index = P_CONST_VAL[P_BIT_INDEX];
        if (P_RANGE_HI >= P_LSB_RANGE) range_out_msb_lsb = P_CONST_VAL[P_RANGE_HI:P_LSB_RANGE];
        else range_out_msb_lsb = P_CONST_VAL[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = P_CONST_VAL[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = P_CONST_VAL[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module LocalparamSel #(
    localparam logic [15:0] LP_CONST_VAL = 16'h5678,
    parameter int P_BIT_INDEX = 5,
    parameter int P_RANGE_HI = 7,
    parameter int P_LSB_RANGE = 0,
    parameter int P_PLUS_START = 4,
    parameter int P_PLUS_WIDTH = 8,
    parameter int P_MINUS_START = 11,
    parameter int P_MINUS_WIDTH = 8
) (
    input logic [3:0] index_bit_var,
    output logic bit_out_var_index,
    output logic bit_out_param_index,
    output logic [($abs(P_RANGE_HI - P_LSB_RANGE)) : 0] range_out_msb_lsb,
    output logic [(P_PLUS_WIDTH - 1) : 0] range_out_plus,
    output logic [(P_MINUS_WIDTH - 1) : 0] range_out_minus
);
    localparam int RANGE_WIDTH = $abs(P_RANGE_HI - P_LSB_RANGE) + 1;
    localparam int PLUS_WIDTH = P_PLUS_WIDTH;
    localparam int MINUS_WIDTH = P_MINUS_WIDTH;
    always_comb begin
         bit_out_var_index = 1'bX;
         bit_out_param_index = 1'bX;
         range_out_msb_lsb = {RANGE_WIDTH {'X'}};
         range_out_plus = {PLUS_WIDTH {'X'}};
         range_out_minus = {MINUS_WIDTH {'X'}};
         if ($isknown(index_bit_var))
             bit_out_var_index = LP_CONST_VAL[index_bit_var];
        bit_out_param_index = LP_CONST_VAL[P_BIT_INDEX];
        if (P_RANGE_HI >= P_LSB_RANGE) range_out_msb_lsb = LP_CONST_VAL[P_RANGE_HI:P_LSB_RANGE];
        else range_out_msb_lsb = LP_CONST_VAL[P_LSB_RANGE:P_MSB_RANGE];
        range_out_plus = LP_CONST_VAL[P_PLUS_START +: P_PLUS_WIDTH];
        range_out_minus = LP_CONST_VAL[P_MINUS_START -: P_MINUS_WIDTH];
    end
endmodule
module NestedVectorSel (
    input logic [15:0] vec_in,
    input logic [3:0] inner_bit,
    output logic bit_out
);
    localparam int OUTER_HI = 10;
    localparam int OUTER_LO = 5;
    logic [15:0] my_vec = vec_in;
    logic [OUTER_HI-OUTER_LO:0] selected_range;
    localparam int SELECTED_RANGE_BITS = $bits(selected_range);
    always_comb begin
        selected_range = my_vec[OUTER_HI:OUTER_LO];
        bit_out = 1'bX;
        if ($isknown(inner_bit) && inner_bit >= 0 && inner_bit < SELECTED_RANGE_BITS) begin
            bit_out = selected_range[inner_bit];
        end
    end
endmodule
module NestedVectorSel_ParamInner #(
    parameter int OUTER_HI = 10,
    parameter int OUTER_LO = 5,
    parameter int INNER_BIT_PARAM = 2
) (
    input logic [15:0] vec_in,
    output logic bit_out_param_inner
);
     logic [15:0] my_vec = vec_in;
     localparam logic [$abs(OUTER_HI - OUTER_LO) : 0] selected_range_param = my_vec[OUTER_HI:OUTER_LO];
     always_comb begin
        bit_out_param_inner = selected_range_param[INNER_BIT_PARAM];
     end
endmodule
module IntSel (
    input int val_in,
    input int index,
    output logic bit_out
);
    int my_int = val_in;
    localparam int INT_LOW = $low(my_int);
    localparam int INT_HIGH = $high(my_int);
    always_comb begin
        bit_out = 1'bX;
        if ($isknown(index) && index >= INT_LOW && index <= INT_HIGH) begin
             bit_out = my_int[index];
        end
    end
endmodule
module LogicIndexPartSel_Plus (
    input logic [7:0] vec_in,
    input logic [2:0] start_index,
    parameter int P_WIDTH = 4,
    output logic [(P_WIDTH - 1) : 0] part_out
);
    logic [7:0] my_vec = vec_in;
    localparam int PART_WIDTH = P_WIDTH;
    always_comb begin
        part_out = {PART_WIDTH{1'bX}};
        part_out = my_vec[start_index +: P_WIDTH];
    end
endmodule
module LogicIndexPartSel_Minus (
    input logic [7:0] vec_in,
    input logic [2:0] start_index,
    parameter int P_WIDTH = 4,
    output logic [(P_WIDTH - 1) : 0] part_out
);
    logic [7:0] my_vec = vec_in;
    localparam int PART_WIDTH = P_WIDTH;
    always_comb begin
         part_out = {PART_WIDTH{1'bX}};
         part_out = my_vec[start_index -: P_WIDTH];
    end
endmodule
module VarRangeSel #(
    parameter int P_MSB_RANGE = 10,
    parameter int P_LSB_RANGE = 5
) (
    input logic [15:0] vec_in,
    output logic [($abs(P_MSB_RANGE - P_LSB_RANGE)) : 0] range_out
);
    logic [15:0] my_vec = vec_in;
    localparam int RANGE_WIDTH = $abs(P_MSB_RANGE - P_LSB_RANGE) + 1;
    always_comb begin
        range_out = {RANGE_WIDTH {'X'}};
        if (P_MSB_RANGE >= P_LSB_RANGE) range_out = my_vec[P_MSB_RANGE:P_LSB_RANGE];
        else range_out = my_vec[P_LSB_RANGE:P_MSB_RANGE];
    end
endmodule
module ParamExprPartSel_Plus #(
    parameter int P_START_BASE = 2,
    parameter int P_OFFSET = 3,
    parameter int P_WIDTH = 4
) (
    input logic [15:0] vec_in,
    output logic [(P_WIDTH - 1) : 0] part_out
);
    logic [15:0] my_vec = vec_in;
    localparam int START_INDEX = P_START_BASE + P_OFFSET;
    localparam int PART_WIDTH = P_WIDTH;
     always_comb begin
         part_out = {PART_WIDTH{1'bX}};
         part_out = my_vec[START_INDEX +: P_WIDTH];
     end
endmodule
module ParamExprPartSel_Minus #(
    parameter int P_START_BASE = 10,
    parameter int P_OFFSET = -2,
    parameter int P_WIDTH = 4
) (
    input logic [15:0] vec_in,
    output logic [(P_WIDTH - 1) : 0] part_out
);
    logic [15:0] my_vec = vec_in;
     localparam int START_INDEX = P_START_BASE + P_OFFSET;
     localparam int PART_WIDTH = P_WIDTH;
     always_comb begin
          part_out = {PART_WIDTH{1'bX}};
          part_out = my_vec[START_INDEX -: P_WIDTH];
     end
endmodule
module ConstantTriIndexPartSel_Plus (
    input logic [7:0] vec_in,
    input logic dummy_in,
    output logic [3:0] part_out
);
    logic [7:0] my_vec = vec_in;
    parameter logic [2:0] START_INDEX_PARAM = 3'hX;
    localparam int P_WIDTH = 4;
    localparam int PART_WIDTH = P_WIDTH;
     always_comb begin
         part_out = my_vec[START_INDEX_PARAM +: P_WIDTH];
    end
endmodule
module ConstantTriIndexPartSel_Minus (
    input logic [7:0] vec_in,
    input logic dummy_in,
    output logic [3:0] part_out
);
    logic [7:0] my_vec = vec_in;
    parameter logic [2:0] START_INDEX_PARAM = 3'bZ;
    localparam int P_WIDTH = 4;
    localparam int PART_WIDTH = P_WIDTH;
     always_comb begin
         part_out = my_vec[START_INDEX_PARAM -: P_WIDTH];
    end
endmodule
module WireSel (
    input logic [7:0] wire_in,
    input logic [2:0] index,
    input logic [3:0] start_part,
    output logic bit_out,
    output logic [3:0] part_out
);
    wire [7:0] my_wire = wire_in;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out = 1'bX;
        part_out = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out = my_wire[index];
        part_out = my_wire[start_part +: PART_WIDTH];
    end
endmodule
module AttributeSel (
    input logic [7:0] attr_var_in,
    input logic [2:0] index,
    input logic [3:0] start_part,
    output logic bit_out,
    output logic [3:0] part_out
);
    (* keep *) logic [7:0] my_var_with_attr = attr_var_in;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out = 1'bX;
        part_out = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out = my_var_with_attr[index];
        part_out = my_var_with_attr[start_part +: PART_WIDTH];
    end
endmodule
module SelRangeWarning #(
    parameter int P_MSB = 5,
    parameter int P_LSB = 10
) (
    input logic [15:0] vec_in,
    output logic [($abs(P_LSB - P_MSB)) : 0] range_out
);
    logic [15:0] my_vec = vec_in;
    always_comb begin
        range_out = my_vec[P_MSB:P_LSB];
    end
endmodule
module Packed2DArraySel #(
    parameter int P_OUTER_IDX = 1,
    parameter int P_INNER_BIT_IDX = 5,
    parameter int P_INNER_RANGE_HI = 7,
    parameter int P_INNER_RANGE_LO = 4,
    parameter int P_INNER_PLUS_START = 5,
    parameter int P_INNER_PLUS_WIDTH = 3,
    parameter int P_INNER_MINUS_START = 7,
    parameter int P_INNER_MINUS_WIDTH = 3
) (
    input logic [7:0] data_in [0:1][0:2],
    input logic [1:0] outer_idx_var,
    input logic [2:0] inner_idx_var,
    output logic bit_out_var_outer_var_inner,
    output logic bit_out_param_outer_var_inner,
    output logic bit_out_var_outer_param_inner,
    output logic bit_out_param_outer_param_inner,
    output logic [($abs(P_INNER_RANGE_HI - P_INNER_RANGE_LO)) : 0] range_out_param_outer_param_inner,
    output logic [(P_INNER_PLUS_WIDTH - 1) : 0] plus_out_param_outer_param_inner,
    output logic [(P_INNER_MINUS_WIDTH - 1) : 0] minus_out_param_outer_param_inner
);
    logic [7:0] packed_2d [0:1][0:2] = data_in;
    localparam int INNER_RANGE_WIDTH = $abs(P_INNER_RANGE_HI - P_INNER_RANGE_LO) + 1;
    localparam int INNER_PLUS_WIDTH = P_INNER_PLUS_WIDTH;
    localparam int INNER_MINUS_WIDTH = P_INNER_MINUS_WIDTH;
    always_comb begin
        bit_out_var_outer_var_inner = 1'bX;
        bit_out_param_outer_var_inner = 1'bX;
        bit_out_var_outer_param_inner = 1'bX;
        bit_out_param_outer_param_inner = 1'bX;
        range_out_param_outer_param_inner = {INNER_RANGE_WIDTH {'X'}};
        plus_out_param_outer_param_inner = {INNER_PLUS_WIDTH {'X'}};
        minus_out_param_outer_param_inner = {INNER_MINUS_WIDTH {'X'}};
        if ($isknown(outer_idx_var) && $isknown(inner_idx_var)) begin
            bit_out_var_outer_var_inner = packed_2d[outer_idx_var][inner_idx_var];
        end
        if ($isknown(inner_idx_var)) begin
            bit_out_param_outer_var_inner = packed_2d[P_OUTER_IDX][inner_idx_var];
        end
        if ($isknown(outer_idx_var)) begin
            bit_out_var_outer_param_inner = packed_2d[outer_idx_var][P_INNER_BIT_IDX];
        end
        bit_out_param_outer_param_inner = packed_2d[P_OUTER_IDX][P_INNER_BIT_IDX];
        if (P_INNER_RANGE_HI >= P_INNER_RANGE_LO) range_out_param_outer_param_inner = packed_2d[P_OUTER_IDX][P_INNER_RANGE_HI:P_INNER_RANGE_LO];
        else range_out_param_outer_param_inner = packed_2d[P_OUTER_IDX][P_INNER_RANGE_LO:P_INNER_RANGE_HI];
        plus_out_param_outer_param_inner = packed_2d[P_OUTER_IDX][P_INNER_PLUS_START +: P_INNER_PLUS_WIDTH];
        minus_out_param_outer_param_inner = packed_2d[P_OUTER_IDX][P_INNER_MINUS_START -: P_INNER_MINUS_WIDTH];
    end
endmodule
module Unpacked2DArraySel #(
    parameter int P_OUTER_IDX = 1,
    parameter int P_INNER_BIT_IDX = 5,
    parameter int P_INNER_RANGE_HI = 7,
    parameter int P_INNER_RANGE_LO = 4,
    parameter int P_INNER_PLUS_START = 5,
    parameter int P_INNER_PLUS_WIDTH = 3,
    parameter int P_INNER_MINUS_START = 7,
    parameter int P_INNER_MINUS_WIDTH = 3,
    parameter int P_OUTER_SLICE_HI = 1,
    parameter int P_OUTER_SLICE_LO = 0,
    parameter int P_OUTER_PLUS_START = 0,
    parameter int P_OUTER_PLUS_WIDTH = 2,
    parameter int P_OUTER_MINUS_START = 1,
    parameter int P_OUTER_MINUS_WIDTH = 2
) (
    input logic [7:0] data_in [0:1][0:2],
    input logic [1:0] outer_idx_var,
    input logic [2:0] inner_idx_var,
    output logic [7:0] elem_out_var_outer_var_inner,
    output logic [7:0] elem_out_param_outer_var_inner,
    output logic bit_out_var_outer_param_inner,
    output logic bit_out_param_outer_param_inner,
    output logic [($abs(P_INNER_RANGE_HI - P_INNER_RANGE_LO)) : 0] range_out_param_outer_param_inner,
    output logic [(P_INNER_PLUS_WIDTH - 1) : 0] plus_out_param_outer_param_inner,
    output logic [(P_INNER_MINUS_WIDTH - 1) : 0] minus_out_param_outer_param_inner,
    output int outer_slice_msb_lsb_size,
    output logic [7:0] first_elem_outer_slice_msb_lsb,
    output int outer_slice_plus_size,
    output logic [7:0] first_elem_outer_slice_plus,
    output int outer_slice_minus_size,
    output logic [7:0] first_elem_outer_slice_minus
);
    logic [7:0] unpacked_2d [0:1][0:2] = data_in;
    localparam int INNER_RANGE_WIDTH = $abs(P_INNER_RANGE_HI - P_INNER_RANGE_LO) + 1;
    localparam int INNER_PLUS_WIDTH = P_INNER_PLUS_WIDTH;
    localparam int INNER_MINUS_WIDTH = P_INNER_MINUS_WIDTH;
    localparam int OUTER_PLUS_WIDTH = P_OUTER_PLUS_WIDTH;
    localparam int OUTER_MINUS_WIDTH = P_OUTER_MINUS_WIDTH;
    logic [7:0] outer_sliced_msb_lsb [];
    logic [7:0] outer_sliced_plus [];
    logic [7:0] outer_sliced_minus [];
    always_comb begin
        elem_out_var_outer_var_inner = 8'hXX;
        elem_out_param_outer_var_inner = 8'hXX;
        bit_out_var_outer_param_inner = 1'bX;
        bit_out_param_outer_param_inner = 1'bX;
        range_out_param_outer_param_inner = {INNER_RANGE_WIDTH {'X'}};
        plus_out_param_outer_param_inner = {INNER_PLUS_WIDTH {'X'}};
        minus_out_param_outer_param_inner = {INNER_MINUS_WIDTH {'X'}};
        outer_sliced_msb_lsb = {};
        outer_sliced_plus = {};
        outer_sliced_minus = {};
        outer_slice_msb_lsb_size = 0;
        first_elem_outer_slice_msb_lsb = 8'hXX;
        outer_slice_plus_size = 0;
        first_elem_outer_slice_plus = 8'hXX;
        outer_slice_minus_size = 0;
        first_elem_outer_slice_minus = 8'hXX;
        if ($isknown(outer_idx_var) && $isknown(inner_idx_var)) begin
            elem_out_var_outer_var_inner = unpacked_2d[outer_idx_var][inner_idx_var];
        end
         if ($isknown(inner_idx_var)) begin
            elem_out_param_outer_var_inner = unpacked_2d[P_OUTER_IDX][inner_idx_var];
        end
        if ($isknown(outer_idx_var)) begin
            bit_out_var_outer_param_inner = unpacked_2d[outer_idx_var][P_INNER_BIT_IDX];
        end
        bit_out_param_outer_param_inner = unpacked_2d[P_OUTER_IDX][P_INNER_BIT_IDX];
        if (P_INNER_RANGE_HI >= P_INNER_RANGE_LO) range_out_param_outer_param_inner = unpacked_2d[P_OUTER_IDX][P_INNER_RANGE_HI:P_INNER_RANGE_LO];
        else range_out_param_outer_param_inner = unpacked_2d[P_OUTER_RANGE_LO:P_INNER_RANGE_HI]; 
        plus_out_param_outer_param_inner = unpacked_2d[P_OUTER_IDX][P_INNER_PLUS_START +: P_INNER_PLUS_WIDTH];
        minus_out_param_outer_param_inner = unpacked_2d[P_OUTER_IDX][P_INNER_MINUS_START -: P_INNER_MINUS_WIDTH];
         if (P_OUTER_SLICE_HI >= P_OUTER_SLICE_LO) outer_sliced_msb_lsb = unpacked_2d[P_OUTER_SLICE_HI:P_OUTER_SLICE_LO];
         else outer_sliced_msb_lsb = unpacked_2d[P_OUTER_SLICE_LO:P_OUTER_SLICE_HI];
         outer_slice_msb_lsb_size = outer_sliced_msb_lsb.size();
         first_elem_outer_slice_msb_lsb = (outer_slice_msb_lsb_size > 0) ? outer_sliced_msb_lsb[0] : 8'hXX;
         outer_sliced_plus = unpacked_2d[P_OUTER_PLUS_START +: P_OUTER_PLUS_WIDTH];
         outer_slice_plus_size = outer_sliced_plus.size();
         first_elem_outer_slice_plus = (outer_slice_plus_size > 0) ? sliced_plus[0] : 8'hXX; 
         outer_sliced_minus = unpacked_2d[P_OUTER_MINUS_START -: P_OUTER_MINUS_WIDTH];
         outer_slice_minus_size = outer_sliced_minus.size();
         first_elem_outer_slice_minus = (outer_slice_minus_size > 0) ? outer_sliced_minus[0] : 8'hXX;
    end
endmodule
module ConcatSel (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [3:0] index,
    input logic [3:0] start_part,
    output logic bit_out,
    output logic [3:0] part_out
);
    logic [15:0] concat_vec = {a, b};
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out = 1'bX;
        part_out = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out = concat_vec[index];
        part_out = concat_vec[start_part +: PART_WIDTH];
    end
endmodule
module ReplicateSel (
    input logic [3:0] val_in,
    input logic [4:0] index,
    input logic [4:0] start_part,
    output logic bit_out,
    output logic [3:0] part_out
);
    logic [15:0] replicated_vec = {4{val_in}};
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out = 1'bX;
        part_out = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out = replicated_vec[index];
        part_out = replicated_vec[start_part +: PART_WIDTH];
    end
endmodule
module BinOpSel (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [3:0] index,
    input logic [3:0] start_part,
    output logic bit_out_and,
    output logic [3:0] part_out_or
);
    logic [7:0] and_res = a & b;
    logic [7:0] or_res = a | b;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out_and = 1'bX;
        part_out_or = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out_and = and_res[index];
        part_out_or = or_res[start_part +: PART_WIDTH];
    end
endmodule
module UnOpSel (
    input logic [7:0] val_in,
    input logic [3:0] index,
    input logic [3:0] start_part,
    output logic bit_out_not,
    output logic [3:0] part_out_not
);
    logic [7:0] not_res = ~val_in;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out_not = 1'bX;
        part_out_not = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out_not = not_res[index];
        part_out_not = not_res[start_part +: PART_WIDTH];
    end
endmodule
module CondOpSel (
    input logic sel,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [3:0] index,
    input logic [3:0] start_part,
    output logic bit_out,
    output logic [3:0] part_out
);
    logic [7:0] cond_res = sel ? a : b;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_out = 1'bX;
        part_out = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_out = cond_res[index];
        part_out = cond_res[start_part +: PART_WIDTH];
    end
endmodule
module PackedArrayOfPackedStructSel #(
    parameter int P_INNER_RANGE_LSB = 10,
    parameter int P_INNER_RANGE_WIDTH = 8
) (
    input packed_struct_t packed_struct_arr_in [0:3],
    input logic [1:0] outer_idx,
    input logic [3:0] inner_bit_idx,
    output logic bit_out_var_idx_var_idx,
    output logic [(P_INNER_RANGE_WIDTH - 1) : 0] range_out_var_idx_param_range
);
    packed_struct_t packed_struct_arr [0:3] = packed_struct_arr_in;
    localparam int INNER_RANGE_WIDTH = P_INNER_RANGE_WIDTH;
    always_comb begin
        bit_out_var_idx_var_idx = 1'bX;
        range_out_var_idx_param_range = {INNER_RANGE_WIDTH {'X'}};
        if ($isknown(outer_idx)) begin
            if ($isknown(inner_bit_idx)) begin
                bit_out_var_idx_var_idx = packed_struct_arr[outer_idx].f1[inner_bit_idx]; 
            end
             if (P_INNER_RANGE_WIDTH > 0) begin
                range_out_var_idx_param_range = packed_struct_arr[outer_idx][P_INNER_RANGE_LSB +: P_INNER_RANGE_WIDTH]; 
             end
        end
    end
endmodule
module UnpackedArrayOfPackedStructSel #(
    parameter int P_INNER_RANGE_LSB = 10,
    parameter int P_INNER_RANGE_WIDTH = 8
) (
    input packed_struct_t unpacked_struct_arr_in [0:3],
    input logic [1:0] outer_idx,
    input logic [3:0] inner_bit_idx,
    output logic [31:0] f3_out_var_idx,
    output logic bit_out_var_idx_var_idx,
    output logic [(P_INNER_RANGE_WIDTH - 1) : 0] range_out_var_idx_param_range
);
    packed_struct_t unpacked_struct_arr [0:3] = unpacked_struct_arr_in;
    localparam int INNER_RANGE_WIDTH = P_INNER_RANGE_WIDTH;
    always_comb begin
        f3_out_var_idx = 32'hXXXX_XXXX;
        bit_out_var_idx_var_idx = 1'bX;
        range_out_var_idx_param_range = {INNER_RANGE_WIDTH {'X'}};
        if ($isknown(outer_idx)) begin
            f3_out_var_idx = unpacked_struct_arr[outer_idx].f3; 
            if ($isknown(inner_bit_idx)) begin
                 bit_out_var_idx_var_idx = unpacked_struct_arr[outer_idx].f1[inner_bit_idx]; 
            end
            if (P_INNER_RANGE_WIDTH > 0) begin
                range_out_var_idx_param_range = unpacked_struct_arr[outer_idx][P_INNER_RANGE_LSB +: P_INNER_RANGE_WIDTH]; 
            end
        end
    end
endmodule
module UnpackedArrayOfUnpackedStructSel (
    input unpacked_struct_t unpacked_struct_arr_in [0:3],
    input logic [1:0] outer_idx,
    input logic [3:0] inner_bit_idx,
    output logic [31:0] uf3_out_var_idx,
    output logic bit_out_var_idx_var_idx
);
    unpacked_struct_t unpacked_struct_arr [0:3] = unpacked_struct_arr_in;
    always_comb begin
        uf3_out_var_idx = 32'hXXXX_XXXX;
        bit_out_var_idx_var_idx = 1'bX;
        if ($isknown(outer_idx)) begin
            uf3_out_var_idx = unpacked_struct_arr[outer_idx].uf3; 
            if ($isknown(inner_bit_idx)) begin
                 bit_out_var_idx_var_idx = unpacked_struct_arr[outer_idx].uf1[inner_bit_idx]; 
            end
        end
    end
endmodule
module VectorSel_RangeDirection (
    input logic [7:0] vec_desc_in,
    input logic [0:7] vec_asc_in,
    input logic [2:0] index,
    input logic [2:0] start_plus,
    input logic [2:0] start_minus,
    output logic bit_desc,
    output logic bit_asc,
    output logic [3:0] part_desc_plus,
    output logic [3:0] part_asc_minus
);
    logic [7:0] vec_desc = vec_desc_in;
    logic [0:7] vec_asc = vec_asc_in;
    localparam int PART_WIDTH = 4;
    always_comb begin
        bit_desc = 1'bX;
        bit_asc = 1'bX;
        part_desc_plus = {PART_WIDTH{1'bX}};
        part_asc_minus = {PART_WIDTH{1'bX}};
        if ($isknown(index)) bit_desc = vec_desc[index];
        if ($isknown(index)) bit_asc = vec_asc[index];
        part_desc_plus = vec_desc[start_plus +: PART_WIDTH];
        part_asc_minus = vec_asc[start_minus -: PART_WIDTH];
    end
endmodule
module NegativeWidthParamPartSel #(
    parameter int P_START = 5,
    parameter int P_NEG_WIDTH = -4
) (
    input logic [15:0] vec_in,
    output logic [(($abs(P_NEG_WIDTH) > 0 ? $abs(P_NEG_WIDTH) : 1)-1) : 0] part_out
);
    logic [15:0] my_vec = vec_in;
    localparam int OUT_WIDTH = ($abs(P_NEG_WIDTH) > 0 ? $abs(P_NEG_WIDTH) : 1);
    logic [OUT_WIDTH-1:0] dummy_plus_res;
    logic [OUT_WIDTH-1:0] dummy_minus_res;
    always_comb begin
        dummy_plus_res = my_vec[P_START +: P_NEG_WIDTH];
        dummy_minus_res = my_vec[P_START -: P_NEG_WIDTH];
        part_out = {OUT_WIDTH {'X'}}; 
    end
endmodule
module VariableIndexUnpackedArraySlice (
    input logic [7:0] unpacked_arr_in [0:3],
    input int msb_idx_var,
    input int lsb_idx_var,
    output int slice_size_out,
    output logic [7:0] first_elem_out
);
    logic [7:0] unpacked_arr [0:3] = unpacked_arr_in;
    logic [7:0] sliced_arr [];
    always_comb begin
        slice_size_out = 0;
        first_elem_out = 8'hXX;
        sliced_arr = unpacked_arr[msb_idx_var:lsb_idx_var];
        slice_size_out = sliced_arr.size();
        if (slice_size_out > 0) begin
            first_elem_out = sliced_arr[0];
        end
    end
endmodule
module VariableIndexUnpackedArrayPartSel (
    input logic [7:0] unpacked_arr_in [0:3],
    input int start_idx_var,
    parameter int P_WIDTH = 2,
    output int slice_size_plus_out,
    output logic [7:0] first_elem_plus_out,
    output int slice_size_minus_out,
    output logic [7:0] first_elem_minus_out
);
    logic [7:0] unpacked_arr [0:3] = unpacked_arr_in;
    logic [7:0] sliced_plus_arr [];
    logic [7:0] sliced_minus_arr [];
    always_comb begin
        slice_size_plus_out = 0;
        first_elem_plus_out = 8'hXX;
        slice_size_minus_out = 0;
        first_elem_minus_out = 8'hXX;
        if (P_WIDTH > 0) begin
             sliced_plus_arr = unpacked_arr[start_idx_var +: P_WIDTH];
             sliced_minus_arr = unpacked_arr[start_idx_var -: P_WIDTH];
        end else begin
             sliced_plus_arr = {};
             sliced_minus_arr = {};
        end
        slice_size_plus_out = sliced_plus_arr.size();
        if (slice_size_plus_out > 0) begin
            first_elem_plus_out = sliced_plus_arr[0];
        end
        slice_size_minus_out = sliced_minus_arr.size();
         if (slice_size_minus_out > 0) begin
             first_elem_minus_out = sliced_minus_arr[0];
         end
    end
endmodule
module ScalarMemberSel (
    input mixed_struct_t val_in,
    input int index_on_scalar,
    input int index_on_vector,
    output logic scalar_bit_out,
    output logic vector_bit_out
);
    mixed_struct_t my_struct = val_in;
    always_comb begin
        scalar_bit_out = my_struct.scalar_field[index_on_scalar];
        vector_bit_out = my_struct.vector_field[index_on_vector];
    end
endmodule
module VarRangeSelectError (
    input logic [7:0] vec_in,
    input logic [2:0] msb_idx_var,
    input logic [2:0] lsb_idx_var,
    output logic [7:0] range_out
);
    logic [7:0] my_vec = vec_in;
    always_comb begin
        range_out = my_vec[msb_idx_var:lsb_idx_var];
    end
endmodule
module VarRangeSelectUnpackedArray (
    input logic [7:0] unpacked_arr_in [0:3],
    input int msb_idx_var,
    input int lsb_idx_var,
    output int slice_size_out,
    output logic [7:0] first_elem_out
);
    logic [7:0] unpacked_arr [0:3] = unpacked_arr_in;
    logic [7:0] sliced_arr [];
    always_comb begin
        slice_size_out = 0;
        first_elem_out = 8'hXX;
        sliced_arr = unpacked_arr[msb_idx_var:lsb_idx_var];
        slice_size_out = sliced_arr.size();
        if (slice_size_out > 0) begin
            first_elem_out = sliced_arr[0];
        end
    end
endmodule
module VarWidthPartSelError (
    input logic [15:0] vec_in,
    input int start_idx,
    input int width_var,
    output logic [15:0] part_out
);
    logic [15:0] my_vec = vec_in;
    always_comb begin
        part_out = my_vec[start_idx +: width_var];
    end
endmodule
module AssocArrayPartSelError (
    input int index_key,
    input int width_param,
    input logic [7:0] data_in_default,
    output logic [7:0] data_out_plus,
    output logic [7:0] data_out_minus
);
    logic [7:0] assoc_arr [int];
    always_comb begin
        assoc_arr[10] = data_in_default;
        data_out_plus = 8'hXX;
        data_out_minus = 8'hXX;
        data_out_plus = assoc_arr[index_key +: width_param];
        data_out_minus = assoc_arr[index_key -: width_param];
    end
endmodule
module DynArrayPartSelError (
    input int index,
    input int width_param,
    input logic [7:0] data_in_arr [],
    output logic [7:0] data_out_plus,
    output logic [7:0] data_out_minus
);
    logic [7:0] dyn_arr [];
    always_comb begin
        dyn_arr = data_in_arr;
        data_out_plus = 8'hXX;
        data_out_minus = 8'hXX;
        if (dyn_arr.size() > 0) begin
            data_out_plus = dyn_arr[index +: width_param];
            data_out_minus = dyn_arr[index -: width_param];
        end
    end
endmodule
module NestedBitSelError (
    input logic [7:0] vec_in,
    input logic [2:0] index1,
    input logic [0:0] index2,
    output logic bit_out
);
    logic [7:0] my_vec = vec_in;
    logic bit1;
    always_comb begin
        bit1 = my_vec[index1];
        bit_out = bit1[index2];
    end
endmodule
module NestedPartSelError (
     input logic [7:0] vec_in,
     input logic [3:0] index1,
     parameter int width_param = 2,
     output logic [1:0] part_out
);
    logic [7:0] my_vec = vec_in;
    logic bit1;
    localparam int PART_WIDTH = width_param;
    always_comb begin
        bit1 = my_vec[index1];
        part_out = bit1[0 +: width_param];
    end
endmodule
