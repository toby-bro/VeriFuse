module module_integral_float_formats (
  input bit [7:0] in_byte,
  input int in_int,
  input real in_real,
  output bit out_status,
  output string s_integral,
  output string s_float,
  output string s_mixed
);
  localparam int param_int = 42;
  localparam byte param_byte = 8'hAB;
  localparam real param_real = 3.14;
  bit status = 1'b1;
  always_comb begin
    s_integral = $sformatf("Param: %d %h %o %b %x %c", param_int, param_int, param_int, param_byte, param_byte, param_byte);
    s_integral = {s_integral, $sformatf("Input: %d %h %o %b %x %c", in_int, in_int, in_int, in_byte, in_byte, in_byte)};
  end
  always_comb begin
    s_float = $sformatf("Param Real: %e %f %g %t", param_real, param_real, param_real, param_real);
    s_float = {s_float, $sformatf("Input Real: %e %f %g %t", in_real, in_real, in_real, in_real)};
  end
  always_comb begin
    s_mixed = $sformatf("Mixed: %d %f %h %e", in_int, in_real, in_byte, param_real);
  end
  assign out_status = status;
endmodule
class my_class;
  int value;
  function new(int v);
    value = v;
  endfunction
endclass
module module_pointer_string_formats (
  input bit clk,
  input string in_string,
  input bit trigger,
  output bit out_status,
  output string s_pointers,
  output string s_strings
);
  bit status;
  my_class class_handle = null;
  localparam string param_string = "hello";
  always_ff @(posedge clk) begin
    status <= 1'b1;
    if (trigger) begin
      class_handle <= new(456);
    end else begin
      class_handle <= null;
    end
    s_pointers <= $sformatf("Pointer: %p Null Pointer: %p", class_handle, null);
    s_strings <= {$sformatf("Param String: %s", param_string), $sformatf("Input String: %s", in_string)};
  end
  assign out_status = status;
endmodule
module module_strength_raw_formats (
  input logic in_logic_1bit,
  input wire [1:0] in_wire_2bit,
  input bit [7:0] in_bit_8bit,
  input bit trigger,
  output bit out_status,
  output string s_strength,
  output string s_raw_integral,
  output string s_raw_struct,
  output string s_raw_union
);
  wire (strong0, strong1) w_strength = 2'b01;
  typedef struct {
    bit [3:0] field1;
    int field2;
  } my_struct_t;
  my_struct_t unpacked_struct_var;
  typedef union {
    byte b;
    shortint s;
  } my_union_t;
  my_union_t unpacked_union_var;
  localparam logic [3:0] lp_strength = 4'b1z0x;
  bit status = 1'b1;
  always_comb begin
     if (trigger) begin
         unpacked_struct_var = '{field1: 4'b1010, field2: 100};
         unpacked_union_var.b = 8'hFF;
     end else begin
         unpacked_struct_var = '{field1: 4'b0000, field2: 0};
         unpacked_union_var.b = 8'h00;
     end
     s_strength = $sformatf("Strength: %v %v %v %v", in_logic_1bit, in_wire_2bit, w_strength, lp_strength);
  end
  always_comb begin
     s_raw_integral = $sformatf("Raw Integral: %u %z", in_bit_8bit, in_bit_8bit);
     s_raw_struct = $sformatf("Raw Struct: %u %z", unpacked_struct_var, unpacked_struct_var);
     s_raw_union = $sformatf("Raw Union: %u %z", unpacked_union_var, unpacked_union_var);
  end
  assign out_status = status;
endmodule
module module_sformat_options_mismatches (
  input int in_val,
  input real in_real,
  input bit trigger_diagnostics,
  output bit out_status,
  output string s_options,
  output string s_diag_mismatch
);
  bit status = 1'b1;
  typedef struct {
    bit [2:0] f1;
    shortint f2;
  } local_struct_t;
  local_struct_t local_struct_var;
  typedef union {
    int i;
    logic [15:0] l;
  } local_union_t;
  local_union_t local_union_var;
  always_comb begin
    s_options = $sformatf("Options: %08d %d %5h %8x %.2f %08.3e", in_val, in_val, in_val, in_val, in_real, in_real);
  end
  always_comb begin
    s_diag_mismatch = "";
    s_diag_mismatch = $sformatf("Type mismatch: %s", in_val);
    if (trigger_diagnostics) begin
        local_struct_var = '{f1: 3'b110, f2: 1234};
        local_union_var.i = 98765;
    end
  end
  assign out_status = status;
endmodule
module module_display_write_special (
  input int in_data,
  input real in_real_data,
  input bit trigger,
  output bit out_done
);
  typedef struct {
    byte f1;
    longint f2;
  } display_struct_t;
  display_struct_t display_struct_var;
  typedef union {
    shortint s;
    int i;
  } display_union_t;
  display_union_t display_union_var;
  always_comb begin
    if (trigger) begin
        display_struct_var = '{f1: 8'h5A, f2: 1234567890};
        display_union_var.s = 16'hABCD;
        $display(in_data);
        $display(in_real_data);
        $display("Direct args: ", in_data, ", ", in_real_data);
        $display("Formatted data: %d, %f", in_data, in_real_data);
        $display("Scope: %m Library/Def: %l");
        $write("Write data: ");
        $write(in_data, " ");
        $write("Formatted write: %h %e", in_data, in_real_data);
        $write("\n"); 
    end
  end
  assign out_done = trigger; 
endmodule
module module_finish_numbers (
  input bit dummy_in,
  output bit dummy_out
);
  parameter p_finish_0 = 0;
  parameter p_finish_1 = 1;
  parameter p_finish_2 = 2;
  parameter p_finish_other_3 = 3;
  parameter p_finish_large_100 = 100;
  parameter p_finish_neg_minus1 = -1;
  localparam lp_finish_0 = 0;
  localparam lp_finish_1 = 1;
  localparam lp_finish_2 = 2;
  localparam lp_finish_other_5 = 5;
  localparam lp_finish_neg_minus10 = -10;
  assign dummy_out = dummy_in;
endmodule
