module element_select_packed(
    input logic [7:0] in_vec,
    input int index_in,
    output logic out_bit,
    output logic [3:0] out_slice
);
  always_comb begin
    if (index_in >= 0 && index_in < 8)
      out_bit = in_vec[index_in];
    else
      out_bit = 'x; 
  end
  assign out_slice = in_vec[6:3];
endmodule
module element_select_unpacked(
    input [3:0][7:0] in_array, 
    input int index_in,
    output logic [7:0] out_elem
);
  always_comb begin
    if (index_in >= 0 && index_in < 4)
      out_elem = in_array[index_in];
    else
      out_elem = 'x; 
  end
endmodule
module element_select_string(
    input string in_string,
    input int index_in,
    output byte out_byte
);
  always_comb begin
    if (index_in >= 0 && index_in < in_string.len())
      out_byte = in_string[index_in];
    else
      out_byte = 0; 
  end
endmodule
module element_select_queue(
    input int in_val_push,
    input int index_in,
    output int out_val,
    output int q_size
);
  int queue_var[$]; 
  always_comb begin
    if (in_val_push > 0) queue_var.push_back(in_val_push);
    q_size = queue_var.size(); 
    if (index_in >= 0 && index_in < q_size)
      out_val = queue_var[index_in];
    else
      out_val = 0; 
  end
endmodule
module element_select_dynamic_array(
    input int in_size,
    input int in_val,
    input int index_in,
    output int out_val,
    output int da_size
);
  int da_var[]; 
  always_comb begin
    if (in_size > 0) da_var = new[in_size];
    else da_var = new[0];
    if (index_in >= 0 && index_in < da_var.size()) da_var[index_in] = in_val;
    da_size = da_var.size(); 
    if (index_in >= 0 && index_in < da_size)
      out_val = da_var[index_in];
    else
      out_val = 0; 
  end
endmodule
module element_select_associative_array(
    input string in_key,
    input int in_val,
    input string lookup_key,
    output int out_val
);
  int aa_var[string]; 
  always_comb begin
    aa_var[in_key] = in_val;
    out_val = aa_var[lookup_key]; 
  end
endmodule
module range_select_simple_packed(
    input logic [15:0] in_vec,
    output logic [7:0] out_slice_be, 
    output logic [7:0] out_slice_le  // fixed: match declared range
);
  assign out_slice_be = in_vec[7:0]; 
  assign out_slice_le = in_vec[7:0]; // fixed: use [7:0] for both
endmodule
module range_select_indexed_packed(
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_up,   
    output logic [7:0] out_down  
);
  always_comb begin
    if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
      case (width)
        1: out_up = in_vec[start_index +: 1];
        2: out_up = in_vec[start_index +: 2];
        4: out_up = in_vec[start_index +: 4];
        8: out_up = in_vec[start_index +: 8];
        default: out_up = 'x;
      endcase
    end else begin
      out_up = 'x;
    end
    if (start_index >= width - 1 && width > 0 && start_index < 32) begin
      case (width)
        1: out_down = in_vec[start_index -: 1];
        2: out_down = in_vec[start_index -: 2];
        4: out_down = in_vec[start_index -: 4];
        8: out_down = in_vec[start_index -: 8];
        default: out_down = 'x;
      endcase
    end else begin
      out_down = 'x;
    end
  end
endmodule
module range_select_unpacked(
    input [7:0][15:0] in_array, 
    output [3:0][15:0] out_slice 
);
  assign out_slice = in_array[3:0]; // fixed: use [3:0] to match range
endmodule
module range_select_dynamic_array(
    input int in_size,
    input int start_index,
    input int end_index,
    output int out_slice_first, 
    output int da_size
);
  int da_var[]; 
  always_comb begin
    int temp_da[];
    if (in_size > 0) da_var = new[in_size];
    else da_var = new[0];
    foreach(da_var[i]) da_var[i] = i;
    da_size = da_var.size(); 
    // Only allow constant range for dynamic array slice
    if (start_index >= 0 && end_index >= 0 && start_index < da_size && end_index < da_size && start_index <= end_index) begin
      temp_da = new[end_index-start_index+1];
      for (int i = 0; i <= end_index-start_index; i++)
        temp_da[i] = da_var[start_index+i];
      if (temp_da.size() > 0) out_slice_first = temp_da[0]; 
      else out_slice_first = 0;
    end else begin
      out_slice_first = 0; 
    end
  end
endmodule
module range_select_queue(
    input int in_val_push,
    input int start_index,
    input int end_index,
    output int out_slice_first, 
    output int q_size
);
  int queue_var[$]; 
  always_comb begin
    int temp_q[$];
    if (in_val_push > 0) queue_var.push_back(in_val_push);
    q_size = queue_var.size(); 
    // Only allow constant range for queue slice
    if (start_index >= 0 && end_index >= 0 && start_index <= end_index && end_index < q_size) begin
      for (int i = 0; i <= end_index-start_index; i++)
        temp_q.push_back(queue_var[start_index+i]);
      if (temp_q.size() > 0) out_slice_first = temp_q[0]; 
      else out_slice_first = 0;
    end else begin
      out_slice_first = 0; 
    end
  end
endmodule
module member_access_struct(
    input int in_val1,
    input byte in_val2,
    output int out_val1,
    output byte out_val2
);
  typedef struct packed {
    int a;
    byte b;
  } my_packed_struct;
  typedef struct {
    int c;
    byte d;
  } my_unpacked_struct;
  my_packed_struct packed_var;
  my_unpacked_struct unpacked_var;
  always_comb begin
    packed_var.a = in_val1;
    packed_var.b = in_val2;
    unpacked_var.c = in_val1 + 1;
    unpacked_var.d = in_val2 + 1;
    out_val1 = unpacked_var.c;
    out_val2 = unpacked_var.d;
  end
endmodule
module member_access_packed_union(
    input bit select_a,
    input logic [31:0] in_val,
    output logic [31:0] out_val
);
  typedef union packed {
    logic [31:0] a; 
    logic [31:0] b; // fixed: match width
  } my_packed_union;
  my_packed_union union_var;
  always_comb begin
    if (select_a)
      union_var.a = in_val;
    else
      union_var.b = in_val[31:0];
    out_val = union_var.a;
  end
endmodule
module member_access_unpacked_union(
    input bit select_a,
    input int in_val_int,
    input longint in_val_longint,
    output int out_val_int,
    output longint out_val_longint,
    output int tagged_access_err_val 
);
  typedef union {
    int a; 
    longint b; 
  } my_unpacked_union;
  my_unpacked_union untagged_union_var;
  always_comb begin
    if (select_a)
      untagged_union_var.a = in_val_int; 
    else
      untagged_union_var.b = in_val_longint; 
    out_val_int = untagged_union_var.a;
    out_val_longint = untagged_union_var.b;
  end
  typedef enum { INT_TAG, LONGINT_TAG } union_tag_e;
  typedef union tagged {
    union_tag_e tag;
    longint y;
  } my_tagged_unpacked_union;
  my_tagged_unpacked_union const_tagged_union;
  initial begin
    const_tagged_union.tag = LONGINT_TAG;
    const_tagged_union.y = 100;
  end
  always_comb begin
    static longint correct_access;
    correct_access = const_tagged_union.y;
    tagged_access_err_val = (const_tagged_union.tag == LONGINT_TAG) ? const_tagged_union.y : 0;
  end
endmodule
module member_access_class(
    input int in_val,
    output int out_field,
    output int out_method_result,
    output bit is_null
);
  class MyClass;
    int field = 10; 
    function int get_field(); 
      return field;
    endfunction
    function int get_field_from_this(); 
      return this.field; 
    endfunction
  endclass
  MyClass obj; 
  initial begin : instantiate_class 
    obj = new(); 
  end
  always_comb begin
    is_null = (obj == null); 
    if (obj != null) begin
      out_field = obj.field;
      out_method_result = obj.get_field();
    end else begin
      out_field = 0;
      out_method_result = 0;
    end
  end
endmodule
module member_access_covergroup(
    input logic clk,
    input logic en,
    input int data,
    output int cg_coverage,
    output int option_weight_read
);
  covergroup cg @(posedge clk);
    option.per_instance = 1; 
    option.weight = 1; 
    cp_data: coverpoint data {
      bins val = {10};
      option.weight = 5; 
    }
  endgroup
  cg cg_inst; 
  initial begin : instantiate_cg
    cg_inst = new(); 
  end
  always @(posedge clk) begin 
    static int cp_weight_read = cg_inst.cp_data.option.weight; 
    if (en) begin
       cg_inst.sample(); 
       option_weight_read = cg_inst.option.weight; 
       cp_weight_read = cg_inst.cp_data.option.weight; 
       cg_inst.option.weight = 2; 
       cg_inst.cp_data.option.weight = 6; 
       cg_coverage = cg_inst.cp_data.get_coverage(); 
    end else begin
       option_weight_read = 0;
       cg_coverage = 0;
    end
  end
endmodule
module builtin_array_method(
    input int lookup_val,
    output int out_size,
    output int out_min,
    output int out_index,
    output bit out_found,
    output int out_sum
);
  int da_var[]; 
  always_comb begin
    static int min_val;
    int idx_arr[];
    da_var = new[5]; 
    foreach(da_var[i]) da_var[i] = i * 10; 
    out_size = da_var.size(); 
    min_val = da_var[0];
    foreach(da_var[i]) if (da_var[i] < min_val) min_val = da_var[i];
    out_min = min_val;
    out_sum = da_var.sum(); 
    out_found = (da_var.find() with (item == lookup_val)).size() > 0; // assign bit
    idx_arr = da_var.find_index() with (item == lookup_val); 
    if (idx_arr.size() > 0) out_index = idx_arr[0];
    else out_index = -1;
  end
endmodule
module builtin_queue_method(
    input int in_val_push_b,
    input int in_val_push_f,
    input bit pop_en,
    output int out_val_pop,
    output int q_size,
    output int out_insert_val,
    output int out_delete_val
);
  int queue_var[$]; 
  always_comb begin
    if (in_val_push_b > 0) queue_var.push_back(in_val_push_b);
    if (in_val_push_f > 0) queue_var.push_front(in_val_push_f);
    if (queue_var.size() >= 2) queue_var.insert(1, 99);
    out_insert_val = (queue_var.size() >= 2 && queue_var[1] == 99) ? 99 : 0;
    if (queue_var.size() >= 3) queue_var.delete(2);
    if (pop_en && queue_var.size() > 0) begin
      out_val_pop = queue_var.pop_front();
    end else begin
      out_val_pop = 0;
    end
    q_size = queue_var.size(); 
  end
endmodule
module builtin_string_method(
    input string in_string,
    input int index_in_getc,
    input int index_in_substr_start,
    input int index_in_substr_end,
    output int out_len,
    output byte out_char,
    output string out_substr_val,
    output string out_upper_val
);
  always_comb begin
    out_len = in_string.len(); 
    if (index_in_getc >= 0 && index_in_getc < in_string.len()) begin
      out_char = in_string.getc(index_in_getc);
    end else begin
      out_char = 0;
    end
    if (index_in_substr_start >= 0 && index_in_substr_end >= 0 &&
        index_in_substr_start < in_string.len() && index_in_substr_end < in_string.len() &&
        index_in_substr_start <= index_in_substr_end) begin
         out_substr_val = in_string.substr(index_in_substr_start, index_in_substr_end);
    end else begin
         out_substr_val = "";
    end
    out_upper_val = in_string.toupper();
  end
endmodule
module lvalue_checks_revised(
    input logic [7:0] in_vec_packed,
    input logic [3:0] in_slice,
    input bit in_bit,
    input int in_da_val,
    input int in_struct_val,
    input logic [3:0] in_union_packed_val,
    input int in_union_unpacked_val_int,
    input bit enable_assign,
    output logic dummy_out 
);
  logic [15:0] vec;
  int da_var[]; 
  typedef struct { int x; } my_struct;
  my_struct s;
  typedef union packed { logic [7:0] a; logic [7:0] b; } my_packed_union;
  my_packed_union pu;
  typedef union { int x; longint y; } my_unpacked_union;
  my_unpacked_union uu;
  always @* begin
    dummy_out = 1'b0; 
    if (enable_assign) begin
      vec[7:4] = in_slice;
      dummy_out = dummy_out | vec[7];
      vec[0] = in_bit;
      dummy_out = dummy_out | vec[0];
      da_var = new[5]; 
      if (in_vec_packed[0] >= 0 && in_vec_packed[0] < 5) begin 
         da_var[in_vec_packed[0]] = in_da_val;
         dummy_out = dummy_out | da_var[in_vec_packed[0]][0]; 
      end else begin
         if (da_var.size() > 0) dummy_out = dummy_out | da_var[0][0];
      end
      s.x = in_struct_val;
      dummy_out = dummy_out | s.x[0];
      pu.b = in_union_packed_val;
      dummy_out = dummy_out | pu.b[0];
      uu.x = in_union_unpacked_val_int;
      dummy_out = dummy_out | uu.x[0];
    end
  end
endmodule
module member_access_rand_mode(
    output bit out_rand_mode,
    output int out_rand_val,
    output bit is_null
);
  class MyRandClass;
    rand int rand_var;
    randc bit randc_var;
  endclass
  MyRandClass obj;
  initial begin : instantiate_class
    obj = new(); 
  end
  always_comb begin
    is_null = (obj == null);
    if (obj != null) begin
      out_rand_mode = obj.rand_var.rand_mode();
      out_rand_val = obj.rand_var;
    end else begin
       out_rand_mode = 0;
       out_rand_val = 0;
    end
  end
endmodule
