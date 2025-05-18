module OperatorsAndWidths (
    input logic [7:0] in_8,
    input logic [15:0] in_16,
    input logic [31:0] in_32,
    input logic [63:0] in_64,
    output logic [31:0] out_arith,
    output logic [31:0] out_logic,
    output logic [31:0] out_compare,
    output logic [31:0] out_unary,
    output logic [63:0] out_shift 
);
    logic [31:0] temp_arith;
    logic [31:0] temp_logic;
    logic [63:0] temp_shift;
    assign temp_arith = in_8 + in_16; 
    assign temp_logic = in_16 & in_32; 
    assign out_arith = temp_arith;
    assign out_logic = temp_logic;
    assign out_compare = (in_8 == in_16) ? 1 : 0; 
    assign out_unary = -in_8; 
    assign temp_logic = temp_logic | !in_16; 
    assign out_logic = temp_logic; 
    assign temp_arith = in_32 % 10; 
    assign out_arith = temp_arith; 
    assign temp_shift = in_64 << in_8; 
    assign out_shift = temp_shift;
endmodule
module ConditionalAndCasts (
    input logic condition,
    input logic [15:0] value_a,
    input logic [31:0] value_b,
    output logic [31:0] out_conditional, 
    output logic [63:0] out_explicit 
);
    assign out_conditional = condition ? value_a : value_b;
    logic [63:0] temp_explicit;
    assign temp_explicit = 64'(value_a) + 64'(value_b);
    assign out_explicit = temp_explicit;
    assign out_explicit = 64'(out_conditional);
endmodule
module PackedStructOps (
    input logic [15:0] packed_in,
    input logic [7:0] byte_val,
    output logic [15:0] packed_out,
    output logic [7:0] byte_out 
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair = packed_in;
    assign byte_out = data_pair.high;
    assign data_pair.low = byte_val;
    assign packed_out = data_pair;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule
module ClassAndNullHandling (
    input logic create_obj,
    input logic pass_derived,
    input int method_arg,
    output int method_result, 
    output int class_op_result 
);
    class Base;
        int data = 10;
        virtual function int get_data();
            return data;
        endfunction
        function void set_data(int val);
            data = val;
        endfunction
    endclass
    class Derived extends Base;
        int derived_data = 20;
        function int get_data(); 
            return data + derived_data;
        endfunction
    endclass
    Base base_inst;
    Derived derived_inst;
    Base obj_ref; 
    Base cond_result_wire; 
    always_comb begin
        base_inst = null;
        derived_inst = null;
        obj_ref = null;
        cond_result_wire = null;
        method_result = -1; 
        class_op_result = -2; 
        if (create_obj) begin
            base_inst = new(); 
            derived_inst = new(); 
            obj_ref = pass_derived ? derived_inst : base_inst;
            cond_result_wire = pass_derived ? derived_inst : base_inst;
        end
        if (obj_ref != null) begin
            method_result = obj_ref.get_data(); 
            obj_ref.set_data(method_arg); 
        end
        if (cond_result_wire != null) begin
            class_op_result = cond_result_wire.get_data();
        end
    end 
endmodule
module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out, 
    output logic [7:0] byte_out 
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule
