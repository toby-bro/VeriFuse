module nested_types_mod (
    input logic [31:0] nested_in,
    output logic [7:0] inner_field_o
);
    typedef struct packed {
    logic [7:0] inner_field;
    logic [7:0] padding;
      } inner_struct_t;
      typedef union packed {
    logic [31:0] full_word;
    struct packed {
      logic [15:0] unused;
      inner_struct_t inner_data;
    } outer_fields;
      } outer_union_t;
      outer_union_t nested_var;
      always_comb begin
    nested_var.full_word = nested_in;
      end
      assign inner_field_o = nested_var.outer_fields.inner_data.inner_field;
endmodule

