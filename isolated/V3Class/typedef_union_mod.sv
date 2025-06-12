module typedef_union_mod (
    output logic [7:0] field0_byte_o,
    input logic [15:0] packed_in
);
    typedef union packed {
        logic [15:0] word;
        logic [1:0][7:0] byte_fields;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    always_comb begin
        my_union_var.word = packed_in;
    end
    assign field0_byte_o = my_union_var.byte_fields[0];
endmodule

