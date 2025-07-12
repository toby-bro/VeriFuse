module comb_complex (
    input bit [7:0] a,
    input bit [7:0] b,
    input bit [2:0] c,
    output bit [7:0] x,
    output bit [7:0] y,
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

