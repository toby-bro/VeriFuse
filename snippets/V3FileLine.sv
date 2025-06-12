class MySvData;
    logic [7:0] byte_field;
    integer counter;
    function new(logic [7:0] init_byte, integer init_count);
        byte_field = init_byte;
        counter = init_count;
    endfunction
    function void increment_counter();
        counter = counter + 1;
    endfunction
endclass
module ModuleComb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    logic [7:0] internal_wire;
    assign internal_wire = in1 + in2;
    always_comb begin
        if (internal_wire > 8'd128) begin
            out1 = internal_wire - 1;
        end else begin
            out1 = internal_wire + 1;
        end
        out2 = internal_wire / 2;
    end
endmodule
module ModuleFF (
    input logic clk,
    input logic reset,
    input bit [3:0] in1,
    input bit [3:0] in2,
    output bit [3:0] out1,
    output bit [3:0] out2
);
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg;
    integer unused_int_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg <= START_VAL;
            out1 <= '0;
            out2 <= '0;
            unused_int_var <= 0;
        end else begin
            case ({in1, in2})
                8'h00: ff_reg <= ff_reg;
                8'h01: ff_reg <= in1 + in2;
                default: ff_reg <= MAX_COUNT;
            endcase
            out1 <= ff_reg;
            out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
        end
    end
endmodule
module ModuleLoops (
    input integer in1,
    input integer in2,
    output integer out1,
    output integer out2
);
    integer i;
    integer temp_sum = 0;
    integer temp_prod = 1;
    always_comb begin
        temp_sum = 0;
        for (i = 0; i < 5; i = i + 1) begin
            temp_sum = temp_sum + (in1 + i);
        end
        out1 = temp_sum;
        temp_prod = 1;
        i = 1;
        while (i <= in2 && i < 8) begin
            temp_prod = temp_prod * i;
            i = i + 1;
        end
        out2 = temp_prod;
    end
endmodule
module ModuleRepeatStruct (
    input logic clk,
    input logic reset,
    input int in1,
    output int out1
);
    struct packed {
        logic [7:0] byte_field;
        bit flag;
    } my_struct_var;
    int repeat_counter;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            repeat_counter <= 0;
            my_struct_var <= '0;
            out1 <= 0;
        end else begin
            repeat (3) begin
                repeat_counter <= repeat_counter + 1;
            end
            my_struct_var.byte_field <= in1[7:0];
            my_struct_var.flag <= (in1 > 100);
            out1 <= repeat_counter + my_struct_var.byte_field;
        end
    end
endmodule
module ModuleArrays (
    input logic [7:0] in_array_val,
    input int in_index,
    output logic [7:0] out_packed_array,
    output logic [7:0] out_unpacked_array
);
    logic [15:0][7:0] packed_array;
    logic [7:0] unpacked_array [0:7];
    integer unused_array_index;
    assign packed_array[0] = in_array_val + 1;
    assign unpacked_array[in_index % 8] = in_array_val - 1;
    assign out_packed_array = packed_array[1];
    assign out_unpacked_array = unpacked_array[in_index % 8];
    assign unused_array_index = 5;
endmodule
module ModuleGenerateIf (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val = in_val + 10;
        end else begin : bypass_block
            assign processed_val = in_val;
        end
    endgenerate
    assign out_val = processed_val;
endmodule
module ModuleClassInstantiation (
    input logic clk,
    input logic reset,
    input int in_data,
    output int out_data
);
    MySvData my_object; 
    logic [7:0] byte_field_reg;
    integer counter_reg;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            my_object <= null; 
            byte_field_reg <= '0;
            counter_reg <= 0;
        end else begin
            if (my_object != null) begin
                byte_field_reg <= my_object.byte_field;
                counter_reg <= my_object.counter;
            end else begin
                byte_field_reg <= '0;
                counter_reg <= 0;
            end
        end
    end
    assign out_data = counter_reg + byte_field_reg;
endmodule
module ModuleLineDirective (
    input logic in1,
    output logic out1
);
    logic internal_sig_a;
    logic internal_sig_b;
    logic unused_line_var;
`line 100 "virtual_file_A.sv" 1
    assign internal_sig_a = in1;
`line 20 "virtual_file_B.sv" 1
    assign internal_sig_b = ~internal_sig_a;
    assign unused_line_var = 1'b1;
`line 150 "virtual_file_A.sv" 2
    assign out1 = internal_sig_b;
`line 1 "original_file.sv" 0
endmodule
