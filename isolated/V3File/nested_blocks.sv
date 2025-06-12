module nested_blocks (
    input logic level2_en,
    input logic data_value,
    output logic result_out,
    input logic level1_en
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

