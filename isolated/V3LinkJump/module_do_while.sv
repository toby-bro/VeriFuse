module module_do_while (
    input logic [3:0] in_limit,
    output logic [3:0] out_value
);
    always_comb begin: do_while_block
        logic [3:0] i;
        logic [3:0] current_sum;
        current_sum = 0;
        i = 0;
        if (in_limit == 0) begin
             current_sum = 0; 
        end else begin
            i = 0;
            current_sum = 0;
            current_sum = current_sum + i;
            i = i + 1;
            while (i < in_limit) begin
                current_sum = current_sum + i;
                i = i + 1;
            end
        end
        out_value = current_sum;
    end
endmodule

