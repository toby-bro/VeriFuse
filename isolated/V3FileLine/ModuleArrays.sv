module ModuleArrays (
    output logic [7:0] out_packed_array,
    output logic [7:0] out_unpacked_array,
    input logic [7:0] in_array_val,
    input int in_index
);
    logic [15:0][7:0] packed_array;
    logic [7:0] unpacked_array [0:7];
    integer unused_array_index;
    assign packed_array[0] = in_array_val + 1;
    assign unpacked_array[in_index % 8] = in_array_val - 1;
    assign out_packed_array = packed_array[1];
    assign out_unpacked_array = unpacked_array[in_index % 8];
    assign unused_array_index = 5;
endmodule

