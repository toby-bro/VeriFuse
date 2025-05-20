class MyClass;
      int data;
      function new(int val);
        data = val;
      endfunction
endclass

module module_types (
    output byte byte_out,
    output logic [31:0] real_out_fixed,
    input logic [7:0] data_in_types,
    input shortint si_in,
    input logic reset_in,
    output int int_out
);
    int var_int_internal;
    byte var_byte_internal;
    shortint var_shortint_internal;
    longint var_longint_internal;
    integer var_integer_internal;
    real var_real_internal;
    time var_time_internal;
    logic var_logic_internal;
    wire var_wire_internal;
    logic [3:0] small_packed;
    logic [100:0] large_packed;
    int unpacked_int_array [3:0];
    string var_string;
    static time static_time_val;
    static string static_string_val;
    MyClass my_class_handle;
    assign var_wire_internal = data_in_types[0];
    always_comb begin
        MyClass temp_handle;
        if (data_in_types[0] && (var_int_internal > 10)) begin
            temp_handle = new(var_shortint_internal);
        end else begin
            temp_handle = null;
        end
        my_class_handle = temp_handle;
    end
    always_ff @(posedge data_in_types[7] or negedge reset_in) begin
        if (!reset_in) begin
            var_int_internal <= 0;
            var_byte_internal <= 0;
            var_shortint_internal <= 0;
            var_longint_internal <= 0;
            var_integer_internal <= 0;
            var_real_internal <= 0.0;
            var_time_internal <= 0;
            var_logic_internal <= 0;
            int_out <= 0;
            byte_out <= 0;
            real_out_fixed <= 0;
            static_time_val <= 0;
            small_packed <= 0;
            large_packed <= 0;
            unpacked_int_array <= '{default:0};
            static_string_val <= "";
        end else begin
            var_int_internal <= si_in + data_in_types[3];
            var_byte_internal <= data_in_types[7:0];
            var_shortint_internal <= var_byte_internal;
            var_longint_internal <= {{($signed(var_int_internal) < 0) ? 32'hFFFF_FFFF : 32'h0}, var_int_internal};
            var_integer_internal <= var_int_internal;
            var_real_internal <= $itor(var_shortint_internal) * 1.1;
            var_time_internal <= var_time_internal + 10;
            var_logic_internal <= var_wire_internal;
            static_time_val <= static_time_val + 1;
            unpacked_int_array[0] <= var_int_internal;
            unpacked_int_array[1] <= (my_class_handle != null) ? my_class_handle.data : 0;
            small_packed <= data_in_types[3:0];
            large_packed <= {101{data_in_types[0]}} ^ large_packed;
            int_out <= var_int_internal + var_integer_internal + unpacked_int_array[1];
            byte_out <= var_byte_internal;
            real_out_fixed <= $rtoi(var_real_internal);
        end
    end
endmodule

