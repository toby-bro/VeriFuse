module another_loop (
    input logic i_i3,
    output logic o_o1,
    output logic o_o2,
    input logic i_i1,
    input logic i_i2
);
    logic r_s1, r_s2, r_s3;
    always_comb begin
        r_s1 = r_s3 | i_i1;
        r_s2 = r_s1 & i_i2;
        r_s3 = r_s2 ^ i_i3;
        o_o1 = r_s1 & r_s2;
        o_o2 = r_s3;
    end
endmodule

