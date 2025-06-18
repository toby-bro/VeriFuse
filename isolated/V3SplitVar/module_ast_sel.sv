module module_ast_sel (
    input logic [7:0] input_byte_as,
    input logic [31:0] raw_data_as,
    output logic [7:0] another_byte_out,
    output logic [7:0] extracted_byte_as
);
    logic [31:0] packed_data_as ;
    assign packed_data_as = raw_data_as;
    assign extracted_byte_as = packed_data_as[15:8];
    logic [7:0] another_byte_as;
    assign another_byte_as = packed_data_as[7:0];
    assign packed_data_as[23:16] = input_byte_as;
    assign another_byte_out = another_byte_as;
endmodule

