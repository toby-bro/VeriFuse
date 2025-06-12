typedef struct packed {
    bit [7:0] field1;
    bit [15:0] field2;
} my_struct;
module comb_simple (
    input bit [7:0] in1, in2,
    output bit [7:0] out1, out2
);
    always @* begin
        out1 = in1 & in2;
        out2 = in1 | in2;
    end
endmodule
module comb_complex (
    input bit [7:0] a, b,
    input bit [2:0] c,
    output bit [7:0] x, y,
    output bit [2:0] z
);
    always @* begin
        bit [7:0] temp_sum;
        temp_sum = a + b;
        x = temp_sum << c;
        y = (a ^ b) | {{(8-3){1'b0}}, c};
        z = ~c;
    end
endmodule
module comb_conditional (
    input bit sel,
    input bit [7:0] data1, data2,
    output bit [7:0] result1, result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule
module comb_packed (
    input my_struct packed_in,
    output my_struct packed_out
);
    always @* begin
        packed_out.field1 = packed_in.field2[7:0] + 1;
        packed_out.field2 = ~packed_in.field1;
    end
endmodule
module comb_many_outputs (
    input bit ctrl,
    input bit [7:0] val,
    output bit o0, o1, o2, o3, o4, o5, o6, o7
);
    always @* begin
        o0 = ctrl & val[0];
        o1 = ctrl | val[1];
        o2 = ctrl ^ val[2];
        o3 = ~val[3];
        o4 = ctrl && val[4];
        o5 = ctrl || val[5];
        o6 = val[6];
        o7 = val[7];
    end
endmodule
