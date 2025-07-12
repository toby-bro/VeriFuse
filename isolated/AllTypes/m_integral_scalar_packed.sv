module m_integral_scalar_packed (
    input bit bit_in,
    input byte byte_in,
    input int int_in,
    input integer integer_in,
    input logic logic_in,
    input longint longint_in,
    input reg reg_in,
    input shortint shortint_in,
    input int signed_int_in,
    input time time_in,
    input logic [7:0] unsigned_logic_in,
    input logic [15:0] vec_in,
    output bit bit_out,
    output byte byte_out,
    output int int_out,
    output integer integer_out,
    output logic logic_out,
    output longint longint_out,
    output reg reg_out,
    output shortint shortint_out,
    output int signed_int_out,
    output time time_out,
    output logic [7:0] unsigned_logic_out,
    output logic [15:0] vec_out
);
    byte byte_var;
    int int_var;
    shortint shortint_var;
    longint longint_var;
    integer integer_var;
    time time_var;
    bit bit_var;
    logic logic_var;
    reg reg_var;
    logic [7:0] packed_logic_vec;
    reg signed [3:0] packed_reg_signed_vec;
    bit unsigned [2:0] packed_bit_unsigned_vec;
    int signed_int_var;
    logic [7:0] unsigned_logic_var;
    always_comb begin
        byte_var = byte_in;
        int_var = int_in;
        shortint_var = shortint_in;
        longint_var = longint_in;
        integer_var = integer_in;
        time_var = time_in;
        bit_var = bit_in;
        logic_var = logic_in;
        reg_var = reg_in;
        packed_logic_vec = vec_in[7:0];
        packed_reg_signed_vec = {reg_in, bit_in, logic_in, packed_logic_vec[0]};
        packed_bit_unsigned_vec = {bit_in, logic_in, reg_in};
        signed_int_var = signed_int_in;
        unsigned_logic_var = unsigned_logic_in;
        byte_out = byte_var;
        int_out = int_var;
        shortint_out = shortint_var;
        longint_out = longint_var;
        integer_out = integer_var;
        time_out = time_var;
        bit_out = bit_var;
        logic_out = logic_var;
        reg_out = reg_var;
        vec_out = {packed_logic_vec, packed_logic_vec};
        signed_int_out = signed_int_var;
        unsigned_logic_out = unsigned_logic_var;
    end
endmodule

