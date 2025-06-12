class MyClass;
    int data;
    function new(int val);
        data = val;
    endfunction
endclass

module module_sizes (
    output logic out_1bit,
    output logic [15:0] out_16bit,
    output logic [63:0] out_64bit,
    output logic [31:0] out_real_fixed,
    input logic in1,
    input logic [7:0] in_byte,
    input logic clk,
    input logic reset_n
);
    logic used_as_clock;
    logic var_1bit;
    byte var_byte_int;
    shortint var_shortint_int;
    logic [15:0] var_16bit_logic;
    int var_int_std;
    logic [31:0] var_32bit_logic;
    longint var_longint_std;
    logic [63:0] var_64bit_logic;
    logic [127:0] var_large;
    int unpacked_array [7:0];
    real var_real_std;
    time var_time_std;
    integer var_integer;
    bit single_bit;
    bit [1:0] small_bit_vec;
    logic [3:0] small_packed_logic;
    logic [100:0] large_packed_logic;
    static int static_var_int;
    static logic [7:0] static_byte_reg;
    MyClass my_class_handle;
    always_comb begin
        MyClass temp_handle;
        used_as_clock = clk;
        var_1bit = in1;
        var_byte_int = in_byte[7:0];
        var_shortint_int = var_byte_int;
        var_16bit_logic = {8'b0, var_byte_int};
        var_int_std = $signed(var_shortint_int) + $signed(var_16bit_logic);
        var_32bit_logic = var_int_std;
        var_64bit_logic = var_longint_std - var_longint_std;
        var_large = {64'b0, var_64bit_logic};
        if (in1 && in_byte[0] && (static_var_int > 5)) begin
            temp_handle = new(static_var_int + var_int_std);
        end else begin
            temp_handle = null;
        end
        my_class_handle = temp_handle;
        out_1bit = var_1bit ^ used_as_clock;
        out_16bit = var_16bit_logic + var_shortint_int;
        out_64bit = var_64bit_logic;
        out_real_fixed = $rtoi(var_real_std);
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            var_longint_std <= 0;
            unpacked_array <= '{default: 0};
            var_real_std <= 0.0;
            var_time_std <= 0;
            static_var_int <= 0;
            static_byte_reg <= 0;
            var_integer <= 0;
            single_bit <= 0;
            small_bit_vec <= 0;
            small_packed_logic <= 0;
            large_packed_logic <= 0;
        end else begin
            var_longint_std <= {{($signed(var_32bit_logic) < 0) ? 32'hFFFF_FFFF : 32'h0}, var_32bit_logic};
            unpacked_array[0] <= var_int_std;
            unpacked_array[1] <= (my_class_handle != null) ? my_class_handle.data : 0;
            static_var_int <= static_var_int + 1;
            static_byte_reg <= in_byte ^ static_byte_reg;
            var_real_std <= $itor(var_int_std) + 1.5;
            var_time_std <= var_time_std + 100;
            var_integer <= var_int_std;
            single_bit <= var_1bit;
            small_bit_vec <= {var_1bit, single_bit};
            small_packed_logic <= {4{in1}};
            large_packed_logic <= {101{in_byte[0]}} ^ large_packed_logic;
        end
    end
endmodule

