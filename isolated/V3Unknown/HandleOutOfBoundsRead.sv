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

