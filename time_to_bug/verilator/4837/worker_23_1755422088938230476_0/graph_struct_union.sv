module more_procedural (
    input logic [31:0] p_in1,
    input logic [31:0] p_in2,
    input logic [1:0] p_mode,
    output logic [31:0] p_out
);
    always_comb begin
        case (p_mode)
            2'b00: p_out = (p_in1 + p_in2) * 2;
            2'b01: p_out = (p_in1 - p_in2) / 3; 
            2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
            default: p_out = ~(p_in1 ^ p_in2) + 1;
        endcase
    end
endmodule

module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [31:0] inj_p_in2_1755422089313_78,
    input logic [1:0] inj_p_mode_1755422089313_623,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [31:0] inj_p_out_1755422089313_217
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
    more_procedural more_procedural_inst_1755422089313_5603 (
        .p_out(inj_p_out_1755422089313_217),
        .p_in1(bus_in),
        .p_in2(inj_p_in2_1755422089313_78),
        .p_mode(inj_p_mode_1755422089313_623)
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

