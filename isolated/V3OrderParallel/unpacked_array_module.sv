module unpacked_array_module (
    input wire [1:0] select_idx,
    output wire [3:0] out_element,
    input wire [7:0] in_array_data
);
    logic [3:0] data_array [4];
    always @(*) begin
        data_array[0] = in_array_data[3:0];
        data_array[1] = in_array_data[7:4];
        data_array[2] = 4'd8;
        data_array[3] = 4'd12;
    end
    assign out_element = data_array[select_idx];
endmodule

