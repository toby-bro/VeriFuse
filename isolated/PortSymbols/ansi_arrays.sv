module ansi_arrays (
    input logic [3:0] input_array
);
    always_comb begin
        output_array[0] = {input_array, input_array};
        output_array[1] = {input_array[3:2], input_array[1:0]};
    end
endmodule

