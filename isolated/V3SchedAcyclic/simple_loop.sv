module simple_loop (
    input logic i_a,
    input logic i_en,
    output logic o_z
);
    logic r_b;
    logic r_c;
    always_comb begin
        r_b = r_c ^ i_a;
        r_c = r_b & i_en;
        o_z = r_c | i_a;
    end
endmodule

