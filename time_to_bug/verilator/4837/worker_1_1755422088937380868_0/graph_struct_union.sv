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

module generate_for_block (
    input logic [1:0] selector,
    output logic [7:0] selected_output
);
    wire [7:0] data [3:0]; 
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (selector)
            0: selected_output = data[0];
            1: selected_output = data[1];
            2: selected_output = data[2];
            3: selected_output = data[3];
            default: selected_output = 8'hXX;
        endcase
    end
endmodule

module graph_struct_union #(
    parameter int SEL_PARAM = 6
) (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [7:0] inj_a_aa_1755422089406_652,
    input logic [7:0] inj_b_aa_1755422089406_621,
    input logic [7:0] inj_c_aa_1755422089406_957,
    input logic [1:0] inj_case_expr_1755422089276_377,
    input logic [3:0] inj_data_in_1755422089341_131,
    input int inj_sel_in_1755422089341_507,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [7:0] inj_data_out_1755422089341_324,
    output logic [4:0] inj_internal_out_1755422089276_245,
    output logic [7:0] inj_selected_output_1755422089350_251,
    output logic [7:0] inj_x_aa_1755422089406_54,
    output logic [7:0] inj_y_aa_1755422089406_310,
    output logic [7:0] inj_z_aa_1755422089406_235
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
    // BEGIN: split_combo_blocking_ts1755422089406
    always @(*) begin
        inj_x_aa_1755422089406_54 = inj_a_aa_1755422089406_652 + inj_b_aa_1755422089406_621;
        inj_y_aa_1755422089406_310 = inj_x_aa_1755422089406_54 - inj_c_aa_1755422089406_957;
        inj_z_aa_1755422089406_235 = inj_a_aa_1755422089406_652 * inj_c_aa_1755422089406_957;
    end
    // END: split_combo_blocking_ts1755422089406

    generate_for_block generate_for_block_inst_1755422089350_8878 (
        .selector(inj_case_expr_1755422089276_377),
        .selected_output(inj_selected_output_1755422089350_251)
    );
    // BEGIN: ModuleHierarchy_High_ts1755422089342
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (inj_sel_in_1755422089341_507),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755422089341;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data_ts1755422089341)
        );
    end else begin : gen_low
        int low_data_ts1755422089341;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data_ts1755422089341)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755422089341;
        assign sub_in_ts1755422089341 = inj_data_in_1755422089341_131[i*2 +: 2];
        int temp_int_ts1755422089341;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755422089341)),
            .out_a  (),
            .out_b  (temp_int_ts1755422089341)
        );
        assign inj_data_out_1755422089341_324[i*4 +: 4] = temp_int_ts1755422089341[3:0];
    end
    // END: ModuleHierarchy_High_ts1755422089342

    // BEGIN: case_full_simple_mod_ts1755422089276
    always @* begin
        (* full *)
        case (inj_case_expr_1755422089276_377)
            2'b00: inj_internal_out_1755422089276_245 = 10;
            2'b01: inj_internal_out_1755422089276_245 = 11;
            2'b10: inj_internal_out_1755422089276_245 = 12;
            default: inj_internal_out_1755422089276_245 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755422089276

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

