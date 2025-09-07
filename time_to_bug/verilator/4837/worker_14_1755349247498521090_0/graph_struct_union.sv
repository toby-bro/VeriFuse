interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

module buf_primitive (
    input wire i,
    output wire o
);
    buf b1 (o, i);
endmodule

module comb_simple (
    input bit [7:0] in1,
    input bit [7:0] in2,
    output bit [7:0] out1,
    output bit [7:0] out2
);
    always @* begin
        out1 = in1 & in2;
        out2 = in1 | in2;
    end
endmodule

module mixed_conn_child (
    input logic [7:0] data_in,
    input logic dummy_in,
    output logic dummy_out
);
    logic dummy_internal;
    always_comb dummy_internal = |data_in | dummy_in;
    assign dummy_out = dummy_internal;
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [7:0] inj_addr_1755349247946_317,
    input logic inj_condition_p_1755349247876_821,
    input logic [7:0] inj_data_in_1755349247855_714,
    input bit [7:0] inj_in1_1755349247823_835,
    input bit [7:0] inj_in2_1755349247823_350,
    input wire [7:0] inj_in2_1755349248078_519,
    input wire [3:0] inj_in_a_1755349248068_320,
    input wire [3:0] inj_in_b_1755349248068_169,
    input wire [7:0] inj_in_c_1755349248068_465,
    input logic [2:0] inj_sel_in_1755349247855_410,
    input wire rst,
    output logic [31:0] bus_out,
    output reg [7:0] inj_data_out_1755349247855_54,
    output logic inj_dummy_out_1755349247944_138,
    output wire inj_o_1755349247825_716,
    output bit [7:0] inj_out1_1755349247823_724,
    output wire [7:0] inj_out1_1755349248078_931,
    output bit [7:0] inj_out2_1755349247823_802,
    output wire [7:0] inj_out2_1755349248078_476,
    output logic [15:0] inj_out_concat_1755349248068_868,
    output logic [7:0] inj_out_if_else_1755349248068_266,
    output logic [7:0] inj_out_reg_p_1755349247876_258,
    output logic inj_write_status_1755349247946_95
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    typedef union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } data_u;
    data_u din, dout;
    // BEGIN: multi_always_comb_ts1755349248078
    logic [7:0] intermediate1_ts1755349248078;
    logic [7:0] intermediate2_ts1755349248078;
    always @(*) begin
        intermediate1_ts1755349248078 = inj_in_c_1755349248068_465 & inj_in2_1755349248078_519;
    end
    always @(*) begin
        intermediate2_ts1755349248078 = inj_in_c_1755349248068_465 | inj_in2_1755349248078_519;
    end
    assign inj_out1_1755349248078_931 = intermediate1_ts1755349248078 + 8'd1;
    assign inj_out2_1755349248078_476 = intermediate2_ts1755349248078 - 8'd1;
    // END: multi_always_comb_ts1755349248078

    // BEGIN: module_concat_if_ts1755349248068
    always_comb begin
    inj_out_concat_1755349248068_868 = {inj_in_a_1755349248068_320, inj_in_b_1755349248068_169, inj_in_c_1755349248068_465};
    if (rst) begin
        inj_out_if_else_1755349248068_266 = inj_in_c_1755349248068_465;
    end else begin
        inj_out_if_else_1755349248068_266 = {inj_in_a_1755349248068_320, inj_in_b_1755349248068_169};
    end
    end
    // END: module_concat_if_ts1755349248068

    // BEGIN: module_sequential_writes_ts1755349247946
    my_if vif_bus();
    always_comb begin
        vif_bus.data = inj_data_in_1755349247855_714;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        inj_write_status_1755349247946_95 = vif_bus.ready;
    end
    // END: module_sequential_writes_ts1755349247946

    mixed_conn_child mixed_conn_child_inst_1755349247944_4138 (
        .dummy_in(inj_condition_p_1755349247876_821),
        .dummy_out(inj_dummy_out_1755349247944_138),
        .data_in(inj_data_in_1755349247855_714)
    );
    split_if_empty_then split_if_empty_then_inst_1755349247876_7179 (
        .clk_p(clk),
        .condition_p(inj_condition_p_1755349247876_821),
        .in_val_p(inj_data_in_1755349247855_714),
        .out_reg_p(inj_out_reg_p_1755349247876_258)
    );
    Module_ControlFlow Module_ControlFlow_inst_1755349247855_9896 (
        .clk(clk),
        .data_in(inj_data_in_1755349247855_714),
        .reset_n(rst),
        .sel_in(inj_sel_in_1755349247855_410),
        .data_out(inj_data_out_1755349247855_54)
    );
    buf_primitive buf_primitive_inst_1755349247825_9963 (
        .i(clk),
        .o(inj_o_1755349247825_716)
    );
    comb_simple comb_simple_inst_1755349247823_4440 (
        .in2(inj_in2_1755349247823_350),
        .out1(inj_out1_1755349247823_724),
        .out2(inj_out2_1755349247823_802),
        .in1(inj_in1_1755349247823_835)
    );
    always_comb begin
        din.word         = bus_in;
        dout.word        = 32'h0;
        dout.bytes.byte0 = din.bytes.byte3;
        dout.bytes.byte1 = din.bytes.byte2;
        dout.bytes.byte2 = din.bytes.byte1;
        dout.bytes.byte3 = din.bytes.byte0;
    end
    assign bus_out = dout.word;
endmodule

