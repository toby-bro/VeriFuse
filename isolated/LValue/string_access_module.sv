typedef bit [7:0] byte_t;
module string_access_module (
    input wire in7,
    output logic [7:0] out7
);
    localparam string my_string = "Hello";
    always_comb begin
        static int dynamic_index = $unsigned(in7) % (my_string.len() + 2);
        byte_t result_char;
        result_char = my_string[dynamic_index];
        out7 = result_char;
    end
    logic _dummy_in = in7;
endmodule

