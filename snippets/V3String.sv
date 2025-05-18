class MyStringUtil;
  string internal_string;
  function new(string s);
    this.internal_string = s;
  endfunction
  function string to_lower();
    string res = internal_string;
    byte upper_a = 8'h41;
    byte upper_z = 8'h5a;
    int diff = 8'h61 - upper_a;
    for (int i = 0; i < res.len(); i++) begin
      if (res[i] >= upper_a && res[i] <= upper_z) begin
        res[i] = res[i] + diff;
      end
    end
    return res;
  endfunction
  function string to_upper();
    string res = internal_string;
    byte lower_a = 8'h61;
    byte lower_z = 8'h7a;
    int diff = 8'h41 - lower_a;
    for (int i = 0; i < res.len(); i++) begin
      if (res[i] >= lower_a && res[i] <= lower_z) begin
        res[i] = res[i] + diff;
      end
    end
    return res;
  endfunction
  function string remove_space();
    string res = "";
    byte space_byte = 8'h20;
    for (int i = 0; i < internal_string.len(); i++) begin
      byte char_byte = internal_string[i];
      if (char_byte != space_byte) begin
         res = {res, string'(char_byte)};
      end
    end
    return res;
  endfunction
  function bit starts_with(string prefix);
    if (prefix.len() == 0) return 1;
    if (internal_string.len() < prefix.len()) return 0;
    return internal_string.substr(0, prefix.len()) == prefix;
  endfunction
  function bit ends_with(string suffix);
    if (suffix.len() == 0) return 1;
    if (internal_string.len() < suffix.len()) return 0;
    return internal_string.substr(internal_string.len() - suffix.len(), suffix.len()) == suffix;
  endfunction
  function bit wildmatch_step(byte s_char, byte p_char);
    byte star_char = 8'h2a;
    byte question_char = 8'h3f;
    if (p_char == star_char) return 1;
    if (p_char == question_char) return 1;
    return s_char == p_char;
  endfunction
  function int find_char(byte search_char, int start_pos);
    for (int i = start_pos; i < internal_string.len(); i++) begin
      if (internal_string[i] == search_char) begin
        return i;
      end
    end
    return -1;
  endfunction
  function bit is_identifier_char(byte char_byte);
    byte lower_a = 8'h61;
    byte lower_z = 8'h7a;
    byte upper_a = 8'h41;
    byte upper_z = 8'h5a;
    byte zero = 8'h30;
    byte nine = 8'h39;
    byte underscore = 8'h5f;
    if ((char_byte >= lower_a && char_byte <= lower_z) ||
        (char_byte >= upper_a && char_byte <= upper_z) ||
        (char_byte >= zero && char_byte <= nine) ||
        (char_byte == underscore)) begin
      return 1;
    end
    return 0;
  endfunction
  function bit is_identifier();
    if (internal_string.len() == 0) return 1;
    for (int i = 0; i < internal_string.len(); i++) begin
      if (!is_identifier_char(internal_string[i])) begin
        return 0;
      end
    end
    return 1;
  endfunction
  function bit is_whitespace();
    if (internal_string.len() == 0) return 1;
    for (int i = 0; i < internal_string.len(); i++) begin
      byte char_byte = internal_string[i];
      if (!(char_byte == 8'h20 || char_byte == 8'h09 || char_byte == 8'h0a ||
            char_byte == 8'h0d || char_byte == 8'h0c || char_byte == 8'h0b)) begin
        return 0;
      end
    end
    return 1;
  endfunction
  function int leading_whitespace_count();
    int count = 0;
    for (int i = 0; i < internal_string.len(); i++) begin
      byte char_byte = internal_string[i];
      if (!(char_byte == 8'h20 || char_byte == 8'h09 || char_byte == 8'h0a ||
            char_byte == 8'h0d || char_byte == 8'h0c || char_byte == 8'h0b)) begin
        break;
      end
      count++;
    end
    return count;
  endfunction
  function string a_or_an();
    if (internal_string.len() == 0) return "";
    case (internal_string[0])
      8'h61, 8'h65, 8'h69, 8'h6f, 8'h75,
      8'h41, 8'h45, 8'h49, 8'h4f, 8'h55:
        return "an";
      default: return "a";
    endcase
  endfunction
  function string quote_char(byte target_char, byte escape_char);
    string res = "";
    for (int i = 0; i < internal_string.len(); i++) begin
      byte char_byte = internal_string[i];
      if (char_byte == target_char) begin
        res = {res, string'(escape_char)};
      end
      res = {res, string'(char_byte)};
    end
    return res;
  endfunction
  function string dequote_percent();
    string res = "";
    byte percent_byte = 8'h25;
    byte last_char = 0;
    for (int i = 0; i < internal_string.len(); i++) begin
      byte current_char = internal_string[i];
      if (last_char == percent_byte && current_char == percent_byte) begin
        last_char = 0;
      end else begin
        res = {res, string'(current_char)};
        last_char = current_char;
      end
    end
    return res;
  endfunction
  function string space_unprintable();
    string res = "";
    byte space_byte = 8'h20;
    byte printable_start = 8'h20;
    byte printable_end = 8'h7E;
    for (int i = 0; i < internal_string.len(); i++) begin
      byte char_byte = internal_string[i];
      if (char_byte >= printable_start && char_byte <= printable_end) begin
        res = {res, string'(char_byte)};
      end else begin
        res = {res, string'(space_byte)};
      end
    end
    return res;
  endfunction
  function string dot_concat(string dot_str, string b_str);
     if (b_str.len() == 0) return internal_string;
     if (internal_string.len() == 0) return b_str;
     return {internal_string, dot_str, b_str};
  endfunction
endclass
class MyBitOps;
  logic [31:0] data;
  static const logic [31:0] K_constants [64] = '{
    32'h428a2f98, 32'h71374491, 32'hb5c0fbcf, 32'he9b5dba5, 32'h3956c25b, 32'h59f111f1, 32'h923f82a4,
    32'hab1c5ed5, 32'hd807aa98, 32'h12835b01, 32'h243185be, 32'h550c7dc3, 32'h72be5d74, 32'h80deb1fe,
    32'h9bdc06a7, 32'hc19bf174, 32'he49b69c1, 32'hefbe4786, 32'h0fc19dc6, 32'h240ca1cc, 32'h2de92c6f,
    32'h4a7484aa, 32'h5cb0a9dc, 32'h76f988da, 32'h983e5152, 32'ha831c66d, 32'hb00327c8, 32'hbf597fc7,
    32'hc6e00bf3, 32'hd5a79147, 32'h06ca6351, 32'h14292967, 32'h27b70a85, 32'h2e1b2138, 32'h4d2c6dfc,
    32'h53380d13, 32'h650a7354, 32'h766a0abb, 32'h81c2c92e, 32'h92722c85, 32'ha2bfe8a1, 32'ha81a664b,
    32'hc24b8b70, 32'hc76c51a3, 32'hd192e819, 32'hd6990624, 32'hf40e3585, 32'h106aa070, 32'h19a4c116,
    32'h1e376c08, 32'h2748774c, 32'h34b0bcb5, 32'h391c0cb3, 32'h4ed8aa4a, 32'h5b9cca4f, 32'h682e6ff3,
    32'h748f82ee, 32'h78a5636f, 32'h84c87814, 32'h8cc70208, 32'h90befffa, 32'ha4506ceb, 32'hbef9a3f7,
    32'hc67178f2
  };
  function new(logic [31:0] d);
    this.data = d;
  endfunction
  function logic [31:0] rotate_right(int shift);
    int actual_shift = shift % 32;
    if (actual_shift < 0) actual_shift += 32;
    return (data >> actual_shift) | (data << (32 - actual_shift));
  endfunction
  function logic [31:0] sha_like_ops(logic [31:0] a, logic [31:0] b, logic [31:0] c, int k_idx);
    logic [31:0] s1_r6 = rotate_right(data, 6);
    logic [31:0] s1_r11 = rotate_right(data, 11);
    logic [31:0] s1_r25 = rotate_right(data, 25);
    logic [31:0] s1 = s1_r6 ^ s1_r11 ^ s1_r25;
    logic [31:0] ch = (data & a) | (~data & b);
    logic [31:0] s0_r2 = rotate_right(c, 2);
    logic [31:0] s0_r13 = rotate_right(c, 13);
    logic [31:0] s0_r22 = rotate_right(c, 22);
    logic [31:0] s0 = s0_r2 ^ s0_r13 ^ s0_r22;
    logic [31:0] maj = (c & a) | (c & b) | (a & b);
    logic [31:0] k_val = get_k_constant(k_idx);
    logic [31:0] temp1_like = b + s1 + ch + k_val;
    logic [31:0] temp2_like = s0 + maj;
    return temp1_like + temp2_like;
  endfunction
  function logic [31:0] get_k_constant(int index);
    if (index >= 0 && index < 64) return K_constants[index];
    return 32'h0;
  endfunction
  function logic [31:0] rotate_right_internal(logic [31:0] val, int shift);
      int actual_shift = shift % 32;
      if (actual_shift < 0) actual_shift += 32;
      return (val >> actual_shift) | (val << (32 - actual_shift));
  endfunction
endclass
class MyArrayOps;
  int data_array[16];
  function new(input int arr[16]);
    for(int i=0; i<16; i++) begin
      this.data_array[i] = arr[i];
    end
  endfunction
  function int process_array_sum_xor();
    int result = 0;
    for (int i = 0; i < 16; i++) begin
      result += this.data_array[i];
      result = result ^ (this.data_array[i] >>> 1);
    end
    return result;
  endfunction
  function int calculate_checksum();
    int sum = 0;
    for(int i=0; i < 16; i++) begin
      sum += this.data_array[i];
    end
    return sum;
  endfunction
  function int get_element(int index);
      if (index >= 0 && index < 16) return data_array[index];
      return 0;
  endfunction
endclass
class MySpellUtil;
  int goal_len;
  int cand_len;
  function new(int g, int c);
    this.goal_len = g;
    this.cand_len = c;
  endfunction
  function int calculate_cutoff();
    int max_length = (goal_len > cand_len) ? goal_len : cand_len;
    int min_length = (goal_len < cand_len) ? goal_len : cand_len;
    int cutoff_dist;
    if (max_length <= 1) begin
      cutoff_dist = 0;
    end else if (max_length - min_length <= 1) begin
      int max_div_3 = max_length / 3;
      cutoff_dist = (max_div_3 > 1) ? max_div_3 : 1;
    end else begin
      cutoff_dist = (max_length + 2) / 3;
    end
    return cutoff_dist;
  endfunction
  function int substitution_cost(byte char1, byte char2);
    return (char1 == char2) ? 0 : 1;
  endfunction
  function int calculate_min_step(int deletion, int insertion, int substitution, int transposition, bit enable_transposition);
    int cheapest = (deletion < insertion) ? deletion : insertion;
    cheapest = (cheapest < substitution) ? cheapest : substitution;
    if (enable_transposition) begin
      cheapest = (cheapest < transposition) ? cheapest : transposition;
    end
    return cheapest;
  endfunction
  function int simulate_edit_step(
      int v_one_ago_j,
      int v_one_ago_j_plus_1,
      int v_next_j,
      int v_two_ago_j_minus_1,
      int step_cost,
      bit step_enable_transposition
  );
    int deletion_cost = v_next_j + 1;
    int insertion_cost = v_one_ago_j_plus_1 + 1;
    int local_substitution_cost = v_one_ago_j + step_cost;
    int cheapest = (deletion_cost < insertion_cost) ? deletion_cost : insertion_cost;
    cheapest = (cheapest < local_substitution_cost) ? cheapest : local_substitution_cost;
    if (step_enable_transposition) begin
      int transposition_cost = v_two_ago_j_minus_1 + 1;
      cheapest = (cheapest < transposition_cost) ? cheapest : transposition_cost;
    end
    return cheapest;
  endfunction
  function bit check_best_candidate_threshold(int current_dist, int best_dist, int goal_len_p, int cand_len_param);
      int max_length = (goal_len_p > cand_len_param) ? goal_len_p : cand_len_param;
      int min_length = (goal_len_p < cand_len_param) ? goal_len_p : cand_len_param;
      int min_dist = max_length - min_length;
      int cutoff;
      if (min_dist >= best_dist) return 0;
      cutoff = calculate_cutoff_helper(goal_len_p, cand_len_param);
      if (min_dist > cutoff) return 0;
      if (current_dist < best_dist && current_dist <= cutoff) return 1;
      return 0;
  endfunction
  function int calculate_cutoff_helper(int goal_len_h, int cand_len_h);
      int max_length = (goal_len_h > cand_len_h) ? goal_len_h : cand_len_h;
      int min_length = (goal_len_h < cand_len_h) ? goal_len_h : cand_len_h;
      if (max_length <= 1) return 0;
      if (max_length - min_length <= 1) begin
          int max_div_3 = max_length / 3;
          return (max_div_3 > 1) ? max_div_3 : 1;
      end
      return (max_length + 2) / 3;
  endfunction
endclass
module string_util_module (
  input string in_string,
  input string in_prefix,
  input string in_suffix,
  input string in_dot_str,
  input string in_b_str,
  input byte in_s_char,
  input byte in_p_char,
  input byte in_search_char,
  input int in_start_pos,
  input byte in_quote_target_char,
  input byte in_quote_escape_char,
  input bit [4:0] op_select,
  output string out_string_result,
  output bit out_bool_result,
  output int out_int_result
);
  MyStringUtil string_inst;
  always_comb begin
    string_inst = new(in_string);
    out_string_result = "";
    out_bool_result = 0;
    out_int_result = -1;
    case (op_select)
      5'd0: out_string_result = string_inst.to_lower();
      5'd1: out_string_result = string_inst.remove_space();
      5'd2: out_bool_result = string_inst.starts_with(in_prefix);
      5'd3: out_bool_result = string_inst.wildmatch_step(in_s_char, in_p_char);
      5'd4: out_int_result = string_inst.find_char(in_search_char, in_start_pos);
      5'd5: out_string_result = string_inst.to_upper();
      5'd6: out_bool_result = string_inst.ends_with(in_suffix);
      5'd7: out_bool_result = string_inst.is_identifier();
      5'd8: out_bool_result = string_inst.is_whitespace();
      5'd9: out_int_result = string_inst.leading_whitespace_count();
      5'd10: out_string_result = string_inst.a_or_an();
      5'd11: out_string_result = string_inst.quote_char(in_quote_target_char, in_quote_escape_char);
      5'd12: out_string_result = string_inst.dequote_percent();
      5'd13: out_string_result = string_inst.space_unprintable();
      5'd14: out_string_result = string_inst.dot_concat(in_dot_str, in_b_str);
      default: begin
        out_string_result = "InvalidOp";
        out_bool_result = 0;
        out_int_result = -2;
      end
    endcase
  end
endmodule
module bitwise_ops_module (
  input logic [31:0] in_data,
  input int in_shift,
  input logic [31:0] in_a,
  input logic [31:0] in_b,
  input logic [31:0] in_c,
  input int in_k_idx,
  input bit [2:0] op_select,
  output logic [31:0] out_result
);
  MyBitOps bitwise_inst;
  always_comb begin
    bitwise_inst = new(in_data);
    out_result = 32'hDeadBeef;
    case (op_select)
      3'd0: out_result = bitwise_inst.rotate_right(in_shift);
      3'd1: out_result = bitwise_inst.sha_like_ops(in_a, in_b, in_c, in_k_idx);
      3'd2: out_result = bitwise_inst.get_k_constant(in_k_idx);
      3'd3: out_result = bitwise_inst.rotate_right_internal(in_a, in_shift);
      default: out_result = 32'hDeadBeef;
    endcase
  end
endmodule
module array_ops_module (
  input int in_array [16],
  input int in_index,
  input bit [1:0] op_select,
  output int out_value
);
  MyArrayOps array_inst;
  always_comb begin
    array_inst = new(in_array);
    out_value = 0;
    case (op_select)
      2'd0: out_value = array_inst.process_array_sum_xor();
      2'd1: out_value = array_inst.calculate_checksum();
      2'd2: out_value = array_inst.get_element(in_index);
      default: out_value = -1;
    endcase
  end
endmodule
module spellcheck_util_module (
  input int in_goal_len,
  input int in_cand_len,
  input byte in_char1,
  input byte in_char2,
  input int in_deletion,
  input int in_insertion,
  input int in_substitution,
  input int in_transposition,
  input bit in_enable_transposition,
  input int in_v_one_ago_j,
  input int in_v_one_ago_j_plus_1,
  input int in_v_next_j,
  input int in_v_two_ago_j_minus_1,
  input int in_step_cost,
  input bit in_step_enable_transposition,
  input int in_current_dist,
  input int in_best_dist,
  input int in_goal_len_param,
  input int in_cand_len_param,
  input bit [2:0] op_select,
  output int out_int_result,
  output bit out_bool_result
);
  MySpellUtil spell_inst;
  always_comb begin
    spell_inst = new(in_goal_len, in_cand_len);
    out_int_result = 0;
    out_bool_result = 0;
    case (op_select)
      3'd0: out_int_result = spell_inst.calculate_cutoff();
      3'd1: out_int_result = spell_inst.substitution_cost(in_char1, in_char2);
      3'd2: out_int_result = spell_inst.calculate_min_step(in_deletion, in_insertion, in_substitution, in_transposition, in_enable_transposition);
      3'd3: out_int_result = spell_inst.simulate_edit_step(
                               in_v_one_ago_j,
                               in_v_one_ago_j_plus_1,
                               in_v_next_j,
                               in_v_two_ago_j_minus_1,
                               in_step_cost,
                               in_step_enable_transposition
                              );
      3'd4: out_bool_result = spell_inst.check_best_candidate_threshold(in_current_dist, in_best_dist, in_goal_len_param, in_cand_len_param);
      3'd5: out_int_result = spell_inst.calculate_cutoff_helper(in_goal_len_param, in_cand_len_param);
      default: begin
        out_int_result = -1;
        out_bool_result = 0;
      end
    endcase
  end
endmodule
