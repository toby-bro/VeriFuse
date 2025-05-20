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

