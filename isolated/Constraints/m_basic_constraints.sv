module m_basic_constraints (
    input logic req,
    output logic ack
);
    assign ack = req;
    class c_basic_constraints;
        rand int r_int_a;
        rand int r_int_b;
        rand bit [7:0] r_byte;
        rand bit [3:0] r_nibble;
        rand bit r_bit;
        rand longint r_longint;
        rand int r_real_a_int_equiv; 
        rand int r_time_a_int_equiv; 
        constraint basic_ops_c {
            r_int_a > 10;
            r_int_b < 20;
            r_int_a == r_int_b;
            r_int_a != r_int_b;
            r_int_a >= 5;
            r_int_b <= 25;
            (r_int_a > 15) && (r_int_b < 15);
            r_bit || (r_int_a == 1);
            r_bit -> (r_int_b != 0);
            r_bit == (r_int_a > 0);
            r_int_a + r_int_b == 30;
            r_int_a - r_int_b != 0;
            r_int_a * r_int_b > 0;
            ~r_byte == 8'hF0;
            r_byte & 8'hF == r_nibble;
            r_byte | 8'hF != 0;
            r_byte ^ r_nibble == 0;
            !r_bit == 0;
            +r_int_a > 0;
            -r_int_b < 0;
            r_int_a << 1 > 0;
            r_int_b >> 1 < 10;
            r_byte <<< 2 != 0;
            r_byte >>> 2 != 0;
            r_int_a inside {[1:5], 10, [15:20]};
            r_nibble inside {[4'h0:4'hF]};
            r_int_a inside {r_int_b, r_int_a + 5};
            r_int_a == 123;
            r_byte == '0;
            r_byte == '1;
            r_longint == 10;
            r_real_a_int_equiv == 100; 
            r_time_a_int_equiv == 50; 
            r_int_a == 0; 
            r_byte == 8'hFF; 
        }
    endclass
    c_basic_constraints inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule

