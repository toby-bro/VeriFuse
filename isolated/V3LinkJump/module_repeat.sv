module module_repeat (
    output logic [3:0] out_counter,
    input logic [3:0] in_times
);
    always_comb begin: repeat_block
        logic [3:0] count_val;
        count_val = 0;
        repeat (in_times) begin
            count_val = count_val + 1;
        end
        out_counter = count_val;
    end
endmodule

