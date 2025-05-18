typedef struct {
    logic [7:0] header;
    logic [15:0] data[4];
} my_unpacked_struct_t;
typedef struct {
    logic [7:0] field1;
    logic [15:0] field2[2];
    logic [3:0] field3;
} another_unpacked_struct_t;
module unpacked_assign (
    input logic [31:0] in_packed_arr,
    output logic [31:0] out_packed_arr
);
    logic [7:0] in_arr[4];
    logic [7:0] out_arr[4];
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            in_arr[i] = in_packed_arr[(i * 8) +: 8];
        end
        out_arr = in_arr;
        out_packed_arr = {<<{out_arr}};
    end
endmodule
module unpacked_sel_assign (
    input logic [255:0] in_packed_data,
    input int index1,
    input int index2,
    output logic [255:0] out_packed_data
);
    logic [31:0] in_data[8];
    logic [31:0] out_data[8];
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            in_data[i] = in_packed_data[(i * 32) +: 32];
        end
        out_data = in_data;
        if (index1 >= 0 && index1 < 8 && index2 >= 0 && index2 < 8) begin
            out_data[index1] = in_data[index2];
        end
        out_packed_data = {<<{out_data}};
    end
endmodule
module unpacked_init_assign (
    input logic dummy_in,
    output logic [47:0] out_packed_arr
);
    logic [15:0] init_arr[3];
    always_comb begin
        init_arr = '{0: 16'haaaa, 2: 16'hbbbb, 1: 16'hcccc};
        out_packed_arr = {<<{init_arr}};
    end
endmodule
module unpacked_compare_eq_neq (
    input logic [39:0] in_packed_a,
    input logic [39:0] in_packed_b,
    output logic equal_result,
    output logic nequal_result
);
    logic [7:0] arr_a[5];
    logic [7:0] arr_b[5];
    always_comb begin
        for (int i = 0; i < 5; i++) begin
            arr_a[i] = in_packed_a[(i * 8) +: 8];
            arr_b[i] = in_packed_b[(i * 8) +: 8];
        end
        equal_result = (arr_a == arr_b);
        nequal_result = (arr_a != arr_b);
    end
endmodule
module unpacked_compare_case_eq_neq (
    input logic [15:0] in_packed_a,
    input logic [15:0] in_packed_b,
    output logic case_equal_result,
    output logic case_nequal_result
);
    logic [7:0] arr_a[2];
    logic [7:0] arr_b[2];
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            arr_a[i] = in_packed_a[(i * 8) +: 8];
            arr_b[i] = in_packed_b[(i * 8) +: 8];
        end
        case_equal_result = (arr_a === arr_b);
        case_nequal_result = (arr_a !== arr_b);
    end
endmodule
module unpacked_conditional (
    input logic condition,
    input logic [7:0] in_packed_true,
    input logic [7:0] in_packed_false,
    output logic [7:0] out_packed_result
);
    logic [3:0] arr_true[2];
    logic [3:0] arr_false[2];
    logic [3:0] result_arr[2];
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            arr_true[i] = in_packed_true[(i * 4) +: 4];
            arr_false[i] = in_packed_false[(i * 4) +: 4];
        end
        result_arr = condition ? arr_true : arr_false;
        out_packed_result = {<<{result_arr}};
    end
endmodule
module struct_unpacked_assign (
    input my_unpacked_struct_t in_struct,
    output my_unpacked_struct_t out_struct
);
    always_comb begin
        out_struct = in_struct;
    end
endmodule
module multidim_unpacked (
    input logic [47:0] in_packed_matrix,
    input int row_idx,
    input int col_idx,
    output logic [7:0] selected_elem
);
    logic [7:0] in_matrix[2][3];
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 3; j++) begin
                in_matrix[i][j] = in_packed_matrix[((i * 3 + j) * 8) +: 8];
            end
        end
        if (row_idx >= 0 && row_idx < 2 && col_idx >= 0 && col_idx < 3) begin
             selected_elem = in_matrix[row_idx][col_idx];
        end else begin
             selected_elem = 'x;
        end
    end
endmodule
module struct_aggregate_init (
    input logic dummy_in,
    output another_unpacked_struct_t out_struct
);
    another_unpacked_struct_t temp_struct;
    always_comb begin
        temp_struct.field1 = 8'haa;
        temp_struct.field2[0] = 16'hbbbb;
        temp_struct.field2[1] = 16'hcccc;
        temp_struct.field3 = 4'h1;
        out_struct = temp_struct;
    end
endmodule
module unpacked_packed_slice (
    input logic [47:0] in_packed_arr,
    input int index,
    input int start_bit,
    output logic [7:0] selected_slice
);
    logic [15:0] in_arr[3];
    always_comb begin
        for (int i = 0; i < 3; i++) begin
            in_arr[i] = in_packed_arr[(i * 16) +: 16];
        end
        if (index >= 0 && index < 3 && start_bit >= 0 && start_bit + 8 <= 16) begin
             selected_slice = in_arr[index][start_bit +: 8];
        end else begin
             selected_slice = 'x;
        end
    end
endmodule
module dynamic_array_internal (
    input logic [31:0] data_seed_packed,
    input int read_idx,
    output logic [7:0] read_data
);
    logic [7:0] my_dynamic_array[];
    int array_size;
    always_comb begin
        my_dynamic_array = new [4];
        for(int i=0; i<4; i++) begin
            my_dynamic_array[i] = data_seed_packed[(i*8) +: 8];
        end
        array_size = my_dynamic_array.size();
        if (read_idx >= 0 && read_idx < array_size) begin
            read_data = my_dynamic_array[read_idx];
        end else begin
            read_data = 'x;
        end
    end
endmodule
module queue_internal (
    input logic [31:0] data_seed_packed,
    input int access_idx_in,
    output logic [7:0] data_out
);
    logic [7:0] my_queue[$];
    int queue_size;
    always_comb begin
        my_queue = {};
        my_queue.push_back(data_seed_packed[7:0]);
        my_queue.push_back(data_seed_packed[15:8]);
        my_queue.push_back(data_seed_packed[23:16]);
        my_queue.push_back(data_seed_packed[31:24]);
        queue_size = my_queue.size();
        if (access_idx_in >= 0 && access_idx_in < queue_size) begin
             data_out = my_queue[access_idx_in];
        end else begin
             data_out = 'x;
        end
    end
endmodule
module unpacked_conditional_struct (
    input logic condition,
    input my_unpacked_struct_t in_struct_true,
    input my_unpacked_struct_t in_struct_false,
    output my_unpacked_struct_t out_struct_result
);
    always_comb begin
        out_struct_result = condition ? in_struct_true : in_struct_false;
    end
endmodule
