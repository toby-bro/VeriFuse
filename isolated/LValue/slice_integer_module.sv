module slice_integer_module (
    input wire in1,
    output logic out1
);
    localparam bit [63:0] initial_value = 64'hFEDC_BA98_7654_3210;
    localparam bit [15:0] loaded_slice = initial_value[47:32];
    typedef struct packed {
        bit [31:0] low;
        bit [31:0] high;
    } packed_word_t;
    function automatic packed_word_t modify_slice(packed_word_t data, bit [15:0] new_val);
        packed_word_t result = data;
        result.high[15:0] = new_val;
        return result;
    endfunction
    localparam packed_word_t struct_value = { initial_value[31:0], initial_value[63:32] };
    localparam packed_word_t modified_struct = modify_slice(struct_value, 16'hAAAA);
    always_comb begin
        out1 = modified_struct.high[0];
    end
    logic _dummy_in = in1;
endmodule

