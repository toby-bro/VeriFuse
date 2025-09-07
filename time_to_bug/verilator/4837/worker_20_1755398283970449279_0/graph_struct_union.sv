module ConditionalOps (
    input logic sel,
    input int val_false,
    input int val_true,
    output int out_val
);
    assign out_val = sel ? val_true : val_false;
endmodule

module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [15:0] inj_data0_1755398284307_429,
    input logic [15:0] inj_data1_1755398284307_798,
    input logic inj_sel_1755398284308_853,
    input int inj_val_false_1755398284317_911,
    input int inj_val_true_1755398284317_34,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [15:0] inj_data_out_1755398284308_185,
    output int inj_out_val_1755398284317_427
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
    ConditionalOps ConditionalOps_inst_1755398284317_8584 (
        .val_true(inj_val_true_1755398284317_34),
        .out_val(inj_out_val_1755398284317_427),
        .sel(inj_sel_1755398284308_853),
        .val_false(inj_val_false_1755398284317_911)
    );
    // BEGIN: CombinationalLogicExplicit_ts1755398284313
    always @(inj_sel_1755398284308_853 or inj_data0_1755398284307_429 or inj_data1_1755398284307_798) begin
        if (inj_sel_1755398284308_853) begin
            inj_data_out_1755398284308_185 = inj_data1_1755398284307_798;
        end else begin
            inj_data_out_1755398284308_185 = inj_data0_1755398284307_429;
        end
    end
    // END: CombinationalLogicExplicit_ts1755398284313

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

