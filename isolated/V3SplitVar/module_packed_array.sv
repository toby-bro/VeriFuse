module module_packed_array (
    input logic enable_pa,
    input logic [31:0] input_pa,
    input logic [3:0] input_slice_pa,
    output logic [7:0] output_pa,
    output logic [7:0] output_pa_element1
);
    logic [7:0] my_packed_array[0:3] ;
    always_comb begin
        if (enable_pa) begin
            my_packed_array[0] = input_pa[7:0];
            my_packed_array[1] = input_pa[15:8];
            my_packed_array[2] = input_pa[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = input_slice_pa;
    end
    assign output_pa = my_packed_array[3];
    assign output_pa_element1 = my_packed_array[1];
endmodule

