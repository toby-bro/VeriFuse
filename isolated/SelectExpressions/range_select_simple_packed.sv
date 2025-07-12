module range_select_simple_packed (
    input logic [15:0] in_vec,
    output logic [7:0] out_slice_be,
    output logic [7:0] out_slice_le
);
    assign out_slice_be = in_vec[7:0]; 
    assign out_slice_le = in_vec[7:0]; 
endmodule

