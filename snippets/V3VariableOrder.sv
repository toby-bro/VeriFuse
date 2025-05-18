class MyClass;
  int data;
  function new(int val);
    data = val;
  endfunction
endclass
module module_sizes (
  input logic in1,
  input logic [7:0] in_byte,
  input logic clk,
  input logic reset_n,
  output logic out_1bit,
  output logic [15:0] out_16bit,
  output logic [63:0] out_64bit,
  output logic [31:0] out_real_fixed
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
module module_types (
    input logic [7:0] data_in_types,
    input shortint si_in,
    input logic reset_in,
    output int int_out,
    output byte byte_out,
    output logic [31:0] real_out_fixed
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
module module_affinity (
    input logic [7:0] input_data_aff,
    input logic enable_aff,
    input logic reset_aff,
    input logic clk_aff,
    output logic [7:0] output_comb_aff,
    output logic [7:0] output_ff_aff
);
    logic [7:0] comb_var1;
    logic [7:0] comb_var2;
    logic [7:0] ff1_var1;
    logic [7:0] ff1_var2;
    logic [7:0] ff2_var1;
    logic [7:0] ff2_var2;
    int shared_var;
    logic [7:0] shared_comb_ff1;
    logic [7:0] shared_ff1_ff2;
    static int static_shared_var;
    MyClass my_class_handle1;
    MyClass my_class_handle2;
    always_comb begin
        MyClass temp_handle1, temp_handle2;
        comb_var1 = input_data_aff + (shared_comb_ff1 != 0 ? shared_comb_ff1 : 1);
        comb_var2 = input_data_aff << 1;
        shared_var = $signed(comb_var1) + $signed(comb_var2);
        if (input_data_aff[0] && enable_aff) begin
            temp_handle1 = new(shared_var + static_shared_var);
        end else begin
            temp_handle1 = null;
        end
        my_class_handle1 = temp_handle1;
        if (input_data_aff[1] && enable_aff) begin
            temp_handle2 = new(shared_ff1_ff2 + static_shared_var);
        end else begin
            temp_handle2 = null;
        end
        my_class_handle2 = temp_handle2;
        output_comb_aff = comb_var1 ^ comb_var2;
    end
    always_ff @(posedge clk_aff or posedge reset_aff) begin
        if (reset_aff) begin
            ff1_var1 <= 8'b0;
            ff1_var2 <= 8'b0;
            shared_comb_ff1 <= 8'b0;
        end else begin
            ff1_var1 <= shared_var;
            ff1_var2 <= ff1_var1 + (my_class_handle1 != null ? my_class_handle1.data : 0);
            shared_comb_ff1 <= ff1_var2;
            static_shared_var <= static_shared_var + 1;
        end
    end
    always_ff @(posedge enable_aff or posedge reset_aff) begin
        if (reset_aff) begin
            ff2_var1 <= 8'b0;
            ff2_var2 <= 8'b0;
            output_ff_aff <= 8'b0;
            shared_ff1_ff2 <= 8'b0;
        end else begin
             ff2_var1 <= shared_ff1_ff2;
             ff2_var2 <= ff2_var1 + (my_class_handle2 != null ? my_class_handle2.data : 0);
             shared_ff1_ff2 <= ff2_var2;
             output_ff_aff <= ff2_var2;
             static_shared_var <= static_shared_var + 1;
        end
    end
endmodule
module module_static (
    input logic [3:0] data_in_static,
    input logic enable_static,
    input logic reset_static,
    input logic clk_static,
    output logic [3:0] data_out_static,
    output logic static_flag
);
    static int static_counter;
    static logic [3:0] static_reg;
    static real static_real_val;
    static integer static_integer_val;
    logic [3:0] non_static_reg;
    logic [3:0] comb_var;
    real non_static_real_comb;
    MyClass my_static_handle;
    always_comb begin
        MyClass temp_handle;
        comb_var = static_reg + data_in_static;
        non_static_real_comb = static_real_val * 2.0;
        if (data_in_static[0] && enable_static && (static_counter > 10)) begin
            temp_handle = new(static_counter + non_static_reg[0]);
        end else begin
            temp_handle = null;
        end
        my_static_handle = temp_handle;
        data_out_static = comb_var + non_static_reg + (my_static_handle != null ? my_static_handle.data : 0);
        static_flag = (static_counter > 100);
    end
    always_ff @(posedge clk_static or posedge reset_static) begin
        if (reset_static) begin
            static_counter <= 0;
            static_reg <= 0;
            static_real_val <= 0.0;
            static_integer_val <= 0;
            non_static_reg <= 0;
        end else begin
            static_counter <= static_counter + 1;
            static_reg <= data_in_static;
            static_real_val <= $itor(static_counter) + 0.5;
            static_integer_val <= static_integer_val + 1;
            non_static_reg <= static_reg + data_in_static;
        end
    end
endmodule
