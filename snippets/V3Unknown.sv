module HandleConstantsAndEquality (
    input logic [7:0] i_data,
    output logic o_eq_q,
    output logic o_neq_q,
    output logic o_eqwild_q,
    output logic o_neqwild_q
);
    parameter P_X_CONST = 8'hXX;
    parameter P_Z_CONST = 8'hZZ;
    parameter P_0_X_CONST = 8'b0101_X10X;
    assign o_eq_q = (i_data ==? P_0_X_CONST);
    assign o_neq_q = (i_data !=? P_0_X_CONST);
    assign o_eqwild_q = (i_data ==? P_X_CONST);
    assign o_neqwild_q = (i_data !=? P_Z_CONST);
endmodule
module HandleSystemFunctionsAndCasex (
    input logic [3:0] i_val_sf,
    input logic [2:0] i_val_case,
    output logic o_isunknown,
    output logic [3:0] o_countbits,
    output logic [1:0] o_case_result
);
    assign o_isunknown = $isunknown(i_val_sf);
    assign o_countbits = $countbits(1, i_val_sf);
    always_comb begin
        casez (i_val_case)
            3'b1?0: o_case_result = 2'b01;
            3'b??1: o_case_result = 2'b10;
            default: o_case_result = 2'b11;
        endcase
    end
endmodule
module HandleOutOfBoundsRead (
    input logic [3:0] i_addr_sel,
    input logic [3:0] i_addr_arr,
    input logic [7:0] i_vector,
    output logic o_sel_var_bit,
    output logic [7:0] o_array_var_elem
);
    parameter ARR_SIZE = 4;
    logic [7:0] my_array [0:ARR_SIZE-1];
    assign my_array[0] = 8'd10;
    assign my_array[1] = 8'd20;
    assign my_array[2] = 8'd30;
    assign my_array[3] = 8'd40;
    assign o_sel_var_bit = i_vector[i_addr_sel];
    assign o_array_var_elem = my_array[i_addr_arr];
endmodule
module HandleOutOfBoundsWrite (
    input logic [3:0] i_addr_write,
    input logic [7:0] i_data_write,
    output logic [7:0] o_modified_vec,
    output logic [7:0] o_modified_arr
);
    parameter VEC_SIZE = 8;
    parameter ARR_SIZE = 4;
    reg [VEC_SIZE-1:0] my_vec_r;
    reg [7:0] my_arr_r [0:ARR_SIZE-1];
    assign o_modified_vec = my_vec_r;
    assign o_modified_arr = my_arr_r[0];
    always_comb begin
        my_vec_r[0] = i_data_write[0];
        my_arr_r[0] = i_data_write;
        my_vec_r[i_addr_write] = i_data_write[0];
        my_arr_r[i_addr_write] = i_data_write;
    end
endmodule
