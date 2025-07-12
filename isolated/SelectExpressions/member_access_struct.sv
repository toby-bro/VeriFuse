module member_access_struct (
    input int in_val1,
    input byte in_val2,
    output int out_val1,
    output byte out_val2
);
    typedef struct packed {
        int a;
        byte b;
    } my_packed_struct;
    typedef struct {
        int c;
        byte d;
    } my_unpacked_struct;
    my_packed_struct packed_var;
    my_unpacked_struct unpacked_var;
    always_comb begin
        packed_var.a = in_val1;
        packed_var.b = in_val2;
        unpacked_var.c = in_val1 + 1;
        unpacked_var.d = in_val2 + 1;
        out_val1 = unpacked_var.c;
        out_val2 = unpacked_var.d;
    end
endmodule

