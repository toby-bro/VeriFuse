module typedef_struct_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

