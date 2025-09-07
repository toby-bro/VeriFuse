module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module graph_struct_union #(
    parameter int SEL_PARAM = 6
) (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [3:0] inj_data_in_1755398284286_350,
    input int inj_sel_in_1755398284286_669,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [7:0] inj_data_out_1755398284286_850
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
    // BEGIN: ModuleHierarchy_High_ts1755398284287
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (inj_sel_in_1755398284286_669),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755398284287;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data_ts1755398284287)
        );
    end else begin : gen_low
        int low_data_ts1755398284287;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data_ts1755398284287)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755398284287;
        assign sub_in_ts1755398284287 = inj_data_in_1755398284286_350[i*2 +: 2];
        int temp_int_ts1755398284287;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755398284287)),
            .out_a  (),
            .out_b  (temp_int_ts1755398284287)
        );
        assign inj_data_out_1755398284286_850[i*4 +: 4] = temp_int_ts1755398284287[3:0];
    end
    // END: ModuleHierarchy_High_ts1755398284287

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

