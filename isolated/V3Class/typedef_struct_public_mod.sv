typedef struct packed {
    logic [15:0] word;
    logic [7:0] value;
    logic [7:0] field1;
    logic [7:0] byte_fields;
    int base_member;
    int calculation_result;
    logic [7:0] inner_field;
    logic [7:0] padding;
    int instance_var;
    logic [7:0] field2;
    logic [7:0] f2;
    logic [7:0] temp_f1;
    logic [15:0] unused;
    logic [15:0] param_value;
    logic [31:0] full_word;
    int derived_member;
    logic [7:0] f1;
    int local_instance_val;
} my_public_packed_struct_t;

module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
      } my_public_packed_struct_t;
      my_public_packed_struct_t my_struct_var;
      always_comb begin
    my_struct_var = packed_in;
      end
      assign field2_o = my_struct_var.field2;
endmodule

