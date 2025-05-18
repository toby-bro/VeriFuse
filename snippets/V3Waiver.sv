module SimpleAssign(
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
endmodule
module CombinationalLogic(
    input logic enable,
    input logic [3:0] val_a,
    input logic [3:0] val_b,
    output logic [3:0] result
);
    always_comb begin
        if (enable) begin
            result = val_a + val_b;
        end else begin
            result = 4'h0;
        end
    end
endmodule
module SequentialLogicPlaceholder(
    input logic clk,
    input logic rst,
    input logic [15:0] data_in,
    output logic [15:0] data_out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            data_out <= 16'h0;
        end else begin
            data_out <= data_in;
        end
    end
endmodule
module MultiplePortsAndTypes(
    input bit flag,
    input logic [3:0] small_val,
    input byte b_in,
    output int i_out
);
    logic [7:0] temp_byte;
    always_comb begin
        if (flag) begin
            temp_byte = {4'h0, small_val};
        end else begin
            temp_byte = b_in;
        end
    end
    assign i_out = temp_byte;
endmodule
module IfElseIfChain(
    input logic [1:0] sel_code,
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    output logic [7:0] selected_data
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule
module SimpleLoopExample(
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule
module SynchronousMemory(
    input logic clk,
    input logic rst,
    input logic [4:0] write_address,
    input logic write_en,
    input logic [7:0] write_data,
    input logic [4:0] read_address,
    output logic [7:0] read_data
);
    logic [7:0] mem [0:31];
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            read_data <= 8'h0;
        end else begin
            if (write_en) begin
                mem[write_address] <= write_data;
            end
            read_data <= mem[read_address];
        end
    end
endmodule
module BitwiseOperations(
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] result_and,
    output logic [7:0] result_or,
    output logic [7:0] result_xor
);
    assign result_and = a & b;
    assign result_or = a | c;
    assign result_xor = b ^ c;
endmodule
module ReductionOperations(
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule
module ShiftOperations(
    input logic [7:0] data,
    input logic [2:0] shift_val,
    output logic [7:0] left_shift_log,
    output logic [7:0] right_shift_log,
    output logic [7:0] right_shift_arith
);
    assign left_shift_log = data << shift_val;
    assign right_shift_log = data >> shift_val;
    assign right_shift_arith = $signed(data) >>> shift_val;
endmodule
