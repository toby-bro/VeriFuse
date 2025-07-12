module mod_genvar (
    input logic clk,
    input logic input_val_gen,
    output logic [7:0] out_sum_gen
);
    genvar i;
    logic [7:0] temp_sum_gen = '0;
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_block
            always_ff @(posedge clk) begin
                if (input_val_gen)
                    temp_sum_gen[i] <= temp_sum_gen[i] + 1'b1;
            end
        end
    endgenerate
    assign out_sum_gen = temp_sum_gen;
    class my_class_genvar;
        int index;
        function new(int i_);
            index = i_;
        endfunction
    endclass
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_class_inst
            always_comb begin
                my_class_genvar cls;
                cls = new(i);
            end
        end
    endgenerate
endmodule

