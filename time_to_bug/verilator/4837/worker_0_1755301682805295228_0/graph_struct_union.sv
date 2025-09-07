module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input bit inj_select_a_1755301683136_508,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [31:0] inj_out_val_1755301683136_193
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
    // BEGIN: member_access_packed_union_ts1755301683136
    typedef union packed {
        logic [31:0] a_ts1755301683136; 
        logic [31:0] b_ts1755301683136; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (inj_select_a_1755301683136_508)
            union_var.a_ts1755301683136 = bus_in;
        else
            union_var.b_ts1755301683136 = bus_in[31:0];
        inj_out_val_1755301683136_193 = union_var.a_ts1755301683136;
    end
    // END: member_access_packed_union_ts1755301683136

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

