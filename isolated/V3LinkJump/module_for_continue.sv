module module_for_continue (
    input logic in_odd_only,
    output logic [3:0] out_accumulate
);
    always_comb begin: for_cont_block
        out_accumulate = 0;
        for (int i = 0; i < 10; i++) begin
            if (in_odd_only && (i % 2 == 0)) begin
                continue;
            end
            out_accumulate = out_accumulate + i;
        end
    end
endmodule

