module ansi_basic (
    input logic clk,
    output logic reset_n
);
    always_comb begin
        reset_n = clk;
    end
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic inj_data0_1755351777564_99,
    input logic inj_data1_1755351777564_71,
    input logic inj_sel_1755351777564_214,
    input wire rst,
    output logic [3:0] cnt,
    output logic inj_reset_n_1755351777563_896,
    output logic inj_result_1755351777564_750
);
    multiplexer_2to1 multiplexer_2to1_inst_1755351777564_1416 (
        .result(inj_result_1755351777564_750),
        .data0(inj_data0_1755351777564_99),
        .data1(inj_data1_1755351777564_71),
        .sel(inj_sel_1755351777564_214)
    );
    ansi_basic ansi_basic_inst_1755351777563_2791 (
        .clk(clk),
        .reset_n(inj_reset_n_1755351777563_896)
    );
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

