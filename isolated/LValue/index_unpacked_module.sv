module index_unpacked_module (
    input wire [15:0] in3,
    output logic [7:0] out3
);
    typedef bit [7:0] unpacked_byte_array_t [0:2];
    localparam unpacked_byte_array_t unpacked_array = {8'hAA, 8'hBB, 8'hCC};
    function automatic unpacked_byte_array_t modify_unpacked_element(unpacked_byte_array_t arr, bit [7:0] new_val);
        unpacked_byte_array_t result = arr;
        if (0 >= 0 && 0 <= 2) result[0] = new_val;
        return result;
    endfunction
    localparam bit [7:0] indexed_unpacked_array = unpacked_array[1];
    localparam unpacked_byte_array_t modified_unpacked_array = modify_unpacked_element(unpacked_array, 8'hDD);
    always_comb begin
        if (2 >= 0 && 2 <= 2) out3 = modified_unpacked_array[2];
        else out3 = '0;
    end
    logic [15:0] _dummy_in = in3;
endmodule

