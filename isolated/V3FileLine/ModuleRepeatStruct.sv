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

