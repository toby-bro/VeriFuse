module module_for_break (
    input logic [3:0] in_target,
    output logic [3:0] out_idx
);
    always_comb begin: for_break_block
        out_idx = 0;
        for (int i = 0; i < 10; i++) begin
            out_idx = i;
            if (i == in_target) begin
                break;
            end
        end
    end
endmodule

