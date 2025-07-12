module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

