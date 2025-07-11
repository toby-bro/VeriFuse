typedef enum logic [1:0] { RED, GREEN, BLUE, YELLOW } color_e;
typedef struct packed {
    logic [15:0] field1;
    logic [15:0] field2;
} packed_struct_t;
typedef struct packed {
    logic [15:0] f1;
    logic [15:0] f2;
} similar_packed_struct_t;
typedef union packed {
    logic [31:0] ufield1;
    packed_struct_t ufield2;
} packed_union_t;
class conversion_object;
    int val;
    function new(int v);
        val = v;
    endfunction
endclass
module NumericConversions(
    input  logic signed [31:0] in_signed32,
    input  logic [7:0]         in_unsigned8,
    output logic signed [63:0] out_signed64_widen,
    output logic        [15:0] out_unsigned16_narrow,
    output logic signed  [7:0] out_signed8_sign_cast
);
    conversion_object dummy;
    always_comb begin
        out_signed64_widen    = in_signed32;
        out_unsigned16_narrow = 16'(in_unsigned8);
        out_signed8_sign_cast = signed'(in_unsigned8);
        dummy = new(0);
    end
endmodule
module EnumConversions(
    input  logic [2:0] in_val,
    output color_e     out_enum_explicit,
    output color_e     out_enum_cond
);
    always_comb begin
        out_enum_explicit = color_e'(in_val);
        out_enum_cond     = in_val[0] ? RED : GREEN;
    end
endmodule
module StructUnionConversions(
    input  packed_struct_t in_struct,
    input  packed_union_t  in_union,
    output packed_struct_t out_struct_from_union,
    output packed_union_t  out_union_from_struct
);
    always_comb begin
        out_union_from_struct = packed_union_t'(in_struct);
        out_struct_from_union = packed_struct_t'(in_union);
    end
endmodule
module FloatingConversions(
    input  real    in_real,
    input  int     in_int,
    output longint    out_int_from_real,
    output shortreal  out_float_from_int
);
    always_comb begin
        out_int_from_real  = longint'(in_real);
        out_float_from_int = shortreal'(in_int);
    end
endmodule
module BitstreamConversions(
    input  logic [31:0]    in_bits,
    input  packed_struct_t in_struct,
    output logic [31:0]    out_bits_from_struct,
    output packed_struct_t out_struct_from_bits,
    output conversion_object out_obj
);
    conversion_object local_obj;
    always_comb begin
        out_bits_from_struct = {<<{in_struct}};
        out_struct_from_bits = packed_struct_t'(in_bits);
        local_obj = new(42);
        out_obj   = local_obj;
    end
endmodule
module ComplexConversions(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule
