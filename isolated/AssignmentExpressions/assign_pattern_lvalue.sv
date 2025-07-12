typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
module assign_pattern_lvalue (
    input logic [38:0] in_packed_for_conv,
    input logic [7:0] in_vec,
    output logic out_bit_conv,
    output int out_int_conv,
    output logic [7:0] out_unpacked_struct_repacked,
    output logic [5:0] out_vec_conv
);
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked;
    int int_var;
    logic bit_var;
    logic [5:0] vec_var;
    always_comb begin
        unpacked_s.f1 = in_vec[3:0];
        unpacked_s.f2 = in_vec[4];
        unpacked_s.f3 = in_vec[7:5];
        reg_unpacked_struct_repacked = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var = in_packed_for_conv[31:0];
        bit_var = in_packed_for_conv[32];
        vec_var = in_packed_for_conv[38:33];
        out_unpacked_struct_repacked = reg_unpacked_struct_repacked;
        out_int_conv = int_var;
        out_bit_conv = bit_var;
        out_vec_conv = vec_var;
    end
endmodule

