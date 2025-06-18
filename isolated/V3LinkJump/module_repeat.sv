module module_repeat (
    input logic [3:0] in_times,
    output logic [3:0] out_counter
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

