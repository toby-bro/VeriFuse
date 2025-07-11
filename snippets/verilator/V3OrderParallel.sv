module simple_comb (
    input wire [7:0] in_data,
    output wire [7:0] out_data
);
    wire [7:0] intermediate_a;
    wire [7:0] intermediate_b;
    wire [7:0] intermediate_c;
    assign intermediate_a = in_data + 8'd1;
    assign intermediate_b = intermediate_a << 1;
    assign intermediate_c = intermediate_a >> 1;
    assign out_data = intermediate_b | intermediate_c;
endmodule
module sequential_hazard (
    input wire clk,
    input wire enable_a,
    input wire enable_b,
    input wire [3:0] data_a,
    input wire [3:0] data_b,
    output wire [3:0] result_out
);
    reg [3:0] shared_reg;
    always @(posedge clk) begin
        if (enable_a) begin
            shared_reg <= data_a;
        end
    end
    always @(posedge clk) begin
        if (enable_b) begin
            shared_reg <= data_b;
        end
    end
    assign result_out = shared_reg;
endmodule
module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] upper_byte_out,
    output wire [7:0] lower_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule
module module_with_params #(
    parameter DATA_WIDTH = 8
) (
    input wire [DATA_WIDTH-1:0] param_in,
    output wire [DATA_WIDTH-1:0] param_out
);
    assign param_out = param_in;
endmodule
module simple_logic_a (
    input wire data_a,
    output wire data_b
);
    assign data_b = ~data_a;
endmodule
module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
endmodule
module simple_seq (
    input wire clk,
    input wire reset,
    input wire [2:0] count_in,
    output wire [2:0] count_out
);
    reg [2:0] counter_reg;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_reg <= 3'b000;
        end else begin
            counter_reg <= count_in + 3'b001;
        end
    end
    assign count_out = counter_reg;
endmodule
module packed_struct_module (
    input wire [15:0] in_packed_data,
    output wire [7:0] out_byte
);
    typedef struct packed {
        logic [7:0] byte1;
        logic [7:0] byte2;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = in_packed_data;
    assign out_byte = data_struct.byte1;
endmodule
module unpacked_array_module (
    input wire [7:0] in_array_data,
    input wire [1:0] select_idx,
    output wire [3:0] out_element
);
    logic [3:0] data_array [4];
    always @(*) begin
        data_array[0] = in_array_data[3:0];
        data_array[1] = in_array_data[7:4];
        data_array[2] = 4'd8;
        data_array[3] = 4'd12;
    end
    assign out_element = data_array[select_idx];
endmodule
module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [63:0] wide_sum,
    output wire [7:0] reduce_xor_out,
    output wire [127:0] concat_out
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule
module multi_always_comb (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    logic [7:0] intermediate1;
    logic [7:0] intermediate2;
    always @(*) begin
        intermediate1 = in1 & in2;
    end
    always @(*) begin
        intermediate2 = in1 | in2;
    end
    assign out1 = intermediate1 + 8'd1;
    assign out2 = intermediate2 - 8'd1;
endmodule
