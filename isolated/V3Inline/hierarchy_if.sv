interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module hierarchy_if (
    input logic clk,
    input logic main_in,
    output logic main_out
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

