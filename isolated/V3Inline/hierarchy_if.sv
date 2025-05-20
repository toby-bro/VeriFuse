module hierarchy_if (
    input logic main_in,
    output logic main_out,
    input logic clk
);
    sub_module u_sub (
        .sub_in(main_in),
        .sub_out(main_out)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = main_in;
        if_inst.ready = main_out;
    end
endmodule

