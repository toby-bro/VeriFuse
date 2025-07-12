module module_strength_raw_formats (
    input bit [7:0] in_bit_8bit,
    input logic in_logic_1bit,
    input wire [1:0] in_wire_2bit,
    input bit trigger,
    output bit out_status,
    output string s_raw_integral,
    output string s_raw_struct,
    output string s_raw_union,
    output string s_strength
);
    wire (strong0, strong1) w_strength = 2'b01;
    typedef struct {
        bit [3:0] field1;
        int field2;
    } my_struct_t;
    my_struct_t unpacked_struct_var;
    typedef union {
        byte b;
        shortint s;
    } my_union_t;
    my_union_t unpacked_union_var;
    localparam logic [3:0] lp_strength = 4'b1z0x;
    bit status = 1'b1;
    always_comb begin
        if (trigger) begin
            unpacked_struct_var = '{field1: 4'b1010, field2: 100};
            unpacked_union_var.b = 8'hFF;
        end else begin
            unpacked_struct_var = '{field1: 4'b0000, field2: 0};
            unpacked_union_var.b = 8'h00;
        end
        s_strength = $sformatf("Strength: %v %v %v %v", in_logic_1bit, in_wire_2bit, w_strength, lp_strength);
    end
    always_comb begin
        s_raw_integral = $sformatf("Raw Integral: %u %z", in_bit_8bit, in_bit_8bit);
        s_raw_struct = $sformatf("Raw Struct: %u %z", unpacked_struct_var, unpacked_struct_var);
        s_raw_union = $sformatf("Raw Union: %u %z", unpacked_union_var, unpacked_union_var);
    end
    assign out_status = status;
endmodule

