module module_selection (
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire in_bit,
    output logic [7:0] out_vector_assign,
    output logic out_bit_select,
    output logic [3:0] out_part_select,
    output logic [7:0] out_bitwise_ops,
    input wire [7:0] in_vector
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
endmodule

