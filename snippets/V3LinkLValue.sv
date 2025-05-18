class base_class;
  int data;
endclass
class derived_class extends base_class;
  int extra_data;
endclass
class MyRandClass;
  rand int my_rand_var;
  rand int dist_bi_var;
  rand int dist_tri_var;
  constraint simple_constraint { my_rand_var > 10 && my_rand_var < 100; }
  constraint dist_constraint {
    dist_bi_var dist { 10 := 50, 20 := 50 };
    dist_tri_var dist { [1:5] :/ 1, [6:10] :/ 2 };
  }
endclass
function automatic int my_function;
  input int arg;
  static int static_var = 123;
  begin
    return static_var + arg;
  end
endfunction
module basic_assign_cont (
    input logic in1,
    input logic in2,
    output logic out1,
    output logic out2,
    output logic out3
);
  always_comb begin
    out1 = in1;
    out2 = in2;
  end
  assign (supply1, supply0) out3 = in1 & in2;
endmodule
module selects_array_member_lvalue (
    input logic [7:0] in_vec_rval,
    input logic [2:0] index_bit,
    input logic [2:0] lsb,
    input logic [1:0] arr_index,
    input logic in_bit_val,
    input logic [3:0] in_part_val,
    input logic [3:0] in_array_val,
    input logic in_struct_field_val,
    output logic [7:0] out_vec,
    output logic [3:0] out_array [0:3],
    output struct packed { logic field; logic other; } out_struct_member
);
  logic [7:0] vec_var;
  logic [3:0] array_var [0:3];
  struct packed { logic field; logic other; } struct_var;
  always_comb begin
    vec_var = in_vec_rval;
    for (int i = 0; i < 4; i++) begin
      array_var[i] = '0;
    end
    struct_var = '{default:'0};
    vec_var[index_bit] = in_bit_val;
    vec_var[lsb +: 4] = in_part_val;
    array_var[arr_index] = in_array_val;
    struct_var.field = in_struct_field_val;
    out_vec = vec_var;
    out_array = array_var;
    out_struct_member = struct_var;
  end
endmodule
module inc_dec_lvalue (
    input int in_val,
    output int out_pre_inc,
    output int out_post_inc,
    output int out_pre_dec,
    output int out_post_dec
);
  always_comb begin
    int temp_var_pre_inc = in_val;
    int temp_var_post_inc = in_val;
    int temp_var_pre_dec = in_val;
    int temp_var_post_dec = in_val;
    out_pre_inc = ++temp_var_pre_inc;
    out_post_inc = temp_var_post_inc++;
    out_pre_dec = --temp_var_pre_dec;
    out_post_dec = temp_var_post_dec--;
  end
endmodule
module task_call_lvalue (
    input logic task_in_val,
    output logic task_out_var
);
  task automatic my_task_internal;
    input logic in_arg;
    output logic out_arg;
    begin
      out_arg = in_arg;
    end
  endtask
  always_comb begin
    my_task_internal(task_in_val, task_out_var);
  end
endmodule
module rand_and_constraint_lvalue (
    input logic trigger,
    output int rand_sys_val,
    output int rand_class_val,
    output int dist_bi_val,
    output int dist_tri_val
);
  MyRandClass my_obj;
  always @(*) begin
    if (my_obj == null) begin
      my_obj = new();
    end
    rand_sys_val = $random;
    rand_class_val = my_obj.my_rand_var;
    dist_bi_val = my_obj.dist_bi_var;
    dist_tri_val = my_obj.dist_tri_var;
  end
endmodule
module initial_static_func (
    input int func_input,
    output int func_static_output
);
  always_comb begin
    func_static_output = my_function(func_input);
  end
endmodule
module force_release_lvalue (
    input logic force_val,
    input logic enable_force,
    input logic enable_release,
    output logic forced_var_out
);
  reg forced_var;
  always_comb begin
    forced_var = '0;
    if (enable_force) begin
      force forced_var = force_val;
    end else if (enable_release) begin
      release forced_var;
    end
    forced_var_out = forced_var;
  end
endmodule
module array_element_inc_dec (
    input int address,
    input logic enable_access,
    output int element_val_pre_inc_out,
    output int element_val_post_inc_out,
    output int element_val_pre_dec_out,
    output int element_val_post_dec_out
);
  int memory_pre_inc [0:7];
  int memory_post_inc [0:7];
  int memory_pre_dec [0:7];
  int memory_post_dec [0:7];
  logic [2:0] index_bit;
  initial begin
      for(int i=0; i<8; i++) begin
          memory_pre_inc[i] = 0;
          memory_post_inc[i] = 0;
          memory_pre_dec[i] = 0;
          memory_post_dec[i] = 0;
      end
  end
  always_comb begin
    index_bit = (address >= 0 && address < 8) ? address[2:0] : 0;
    element_val_pre_inc_out = memory_pre_inc[index_bit];
    element_val_post_inc_out = memory_post_inc[index_bit];
    element_val_pre_dec_out = memory_pre_dec[index_bit];
    element_val_post_dec_out = memory_post_dec[index_bit];
    if (enable_access) begin
        ++memory_pre_inc[index_bit];
        memory_post_inc[index_bit]++;
        --memory_pre_dec[index_bit];
        memory_post_dec[index_bit]--;
    end
  end
endmodule
module event_cast_lvalue (
    input logic event_trigger_in,
    input logic enable_cast_in,
    output logic event_fired_out,
    output logic cast_success_out
);
  event my_event;
  reg event_fired_out_reg;
  reg cast_success_out_reg;
  base_class base_h;
  derived_class derived_h;
  base_class source_h;
  initial begin
      base_h = new();
      derived_h = new();
      source_h = derived_h;
  end
  always_comb begin
    event_fired_out_reg = 0;
    if (event_trigger_in) begin
      -> my_event;
      event_fired_out_reg = 1;
    end
    cast_success_out_reg = 0;
    if (enable_cast_in) begin
      cast_success_out_reg = $cast(derived_h, source_h);
    end
  end
  assign event_fired_out = event_fired_out_reg;
  assign cast_success_out = cast_success_out_reg;
endmodule
module sys_task_lvalue_expanded (
    input string sscanf_input_string,
    input string readmemb_filename,
    input string readmemh_filename,
    input int data_to_format_in,
    input int dummy_file_handle_in,
    input string plusargs_search_string,
    input logic [7:0] char_to_unget_in,
    input int fgets_size_in,
    output int sscanf_output_int,
    output int value_plusargs_output_int,
    output int fscanf_output_int,
    output logic [7:0] memory_out_b [0:3],
    output logic [7:0] memory_out_h [0:3],
    output string sformat_out,
    output logic [7:0] fread_out [0:3],
    output int testplusargs_out,
    output string fgets_out_string,
    output int ferror_out,
    output int ungetc_out_status,
    output time time_out
);
  logic [7:0] internal_memory_b [0:3];
  logic [7:0] internal_memory_h [0:3];
  logic [7:0] internal_fread_mem [0:3];
  integer file_handle;
  string sformat_output_string;
  string fgets_output_string_var;
  int test_result;
  int ferror_result;
  int ungetc_result_status_var;
  logic [7:0] local_char_to_unget;
  time current_time;
  always_comb begin
    void'( $sscanf(sscanf_input_string, "%d", sscanf_output_int) );
    void'( $value$plusargs(plusargs_search_string, value_plusargs_output_int) );
    file_handle = (dummy_file_handle_in > 0) ? 32'h8000_0001 : 0;
    if (file_handle != 0) begin
      void'( $fscanf(file_handle, "%d", fscanf_output_int) );
      void'($fread(internal_fread_mem, file_handle));
      void'($fgets(fgets_output_string_var, fgets_size_in, file_handle));
      ferror_result = $ferror(file_handle);
      local_char_to_unget = char_to_unget_in;
      ungetc_result_status_var = $ungetc(local_char_to_unget, file_handle);
    end else begin
        fscanf_output_int = '0;
        internal_fread_mem = '{default:'0};
        fgets_output_string_var = "";
        ferror_result = 0;
        ungetc_result_status_var = -1;
    end
    void'( $readmemb(readmemb_filename, internal_memory_b) );
    void'( $readmemh(readmemh_filename, internal_memory_h) );
    $sformat(sformat_output_string, "Data: %0d", data_to_format_in);
    test_result = $test$plusargs(plusargs_search_string);
    current_time = $time;
    memory_out_b = internal_memory_b;
    memory_out_h = internal_memory_h;
    sformat_out = sformat_output_string;
    fread_out = internal_fread_mem;
    testplusargs_out = test_result;
    fgets_out_string = fgets_output_string_var;
    ferror_out = ferror_result;
    ungetc_out_status = ungetc_result_status_var;
    time_out = current_time;
  end
endmodule
