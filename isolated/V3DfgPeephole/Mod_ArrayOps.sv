module Mod_ArrayOps (
    input wire [1:0] in_const_index,
    input wire [7:0] in_data,
    input wire [1:0] in_index,
    output logic [7:0] out_array_sel_const,
    output logic [7:0] out_array_sel_var
);
    logic [7:0] my_array [3:0];
    always_comb begin
        my_array[0] = in_data;
        my_array[1] = in_data + 8'd1;
        my_array[2] = in_data + 8'd2;
        my_array[3] = in_data + 8'd3;
        out_array_sel_var = my_array[in_index];
        out_array_sel_const = my_array[in_const_index];
    end
endmodule

