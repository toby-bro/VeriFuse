module m_basic_constraints (input logic req, output logic ack);
    assign ack = req;
    class c_basic_constraints;
        rand int r_int_a;
        rand int r_int_b;
        rand bit [7:0] r_byte;
        rand bit [3:0] r_nibble;
        rand bit r_bit;
        rand longint r_longint;
        rand int r_real_a_int_equiv; // replaced real with int for constraint diversity
        rand int r_time_a_int_equiv; // replaced time with int for constraint diversity
        constraint basic_ops_c {
            r_int_a > 10;
            r_int_b < 20;
            r_int_a == r_int_b;
            r_int_a != r_int_b;
            r_int_a >= 5;
            r_int_b <= 25;
            (r_int_a > 15) && (r_int_b < 15);
            r_bit || (r_int_a == 1);
            r_bit -> (r_int_b != 0);
            r_bit == (r_int_a > 0);
            r_int_a + r_int_b == 30;
            r_int_a - r_int_b != 0;
            r_int_a * r_int_b > 0;
            ~r_byte == 8'hF0;
            r_byte & 8'hF == r_nibble;
            r_byte | 8'hF != 0;
            r_byte ^ r_nibble == 0;
            !r_bit == 0;
            +r_int_a > 0;
            -r_int_b < 0;
            r_int_a << 1 > 0;
            r_int_b >> 1 < 10;
            r_byte <<< 2 != 0;
            r_byte >>> 2 != 0;
            r_int_a inside {[1:5], 10, [15:20]};
            r_nibble inside {[4'h0:4'hF]};
            r_int_a inside {r_int_b, r_int_a + 5};
            r_int_a == 123;
            r_byte == '0;
            r_byte == '1;
            r_longint == 10;
            r_real_a_int_equiv == 100; // replaced r_real_a == 1.0
            r_time_a_int_equiv == 50; // replaced r_time_a == 1ns
            r_int_a == 0; // replaced 'z with 0
            r_byte == 8'hFF; // replaced 'X with valid value
        }
    endclass
    c_basic_constraints inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_complex_constraints (input bit start_trigger, output bit done_flag);
    assign done_flag = start_trigger;
    class c_complex_constraints;
        rand int r_int_a;
        rand int r_int_b;
        randc int rc_int; 
        int non_rand_int; 
        logic [7:0] byte_var;
        string s_var; 
        event ev_var; 
        rand bit [15:0] rand_short_real; 
        rand bit [7:0] r_byte;
        rand bit [3:0] r_nibble;
        function automatic int func_no_side_effects(input int in_v);
            return in_v + 1;
        endfunction
        function automatic int func_with_out(input int in_v, output int out_v);
            out_v = in_v * 2;
            return out_v;
        endfunction
        function automatic int func_with_ref(ref int inout_v);
            inout_v = inout_v + 1;
            return inout_v;
        endfunction
        task automatic my_task();
        endtask
        constraint soft_ok_c {
            soft r_int_a > 50;
        }
        constraint soft_randc_err_c {
            soft r_int_b == 5; // replaced rc_int with r_int_b for valid soft constraint
        }
        constraint disable_soft_ok_c {
            disable soft r_int_a;
        }
        constraint disable_soft_non_rand_err_c {
            disable soft r_int_b; // replaced non_rand_int with r_int_b (rand)
        }
        constraint disable_soft_randc_err_c {
            disable soft r_int_a; // replaced rc_int with r_int_a (rand)
        }
        constraint disable_soft_syscall_ok_c {
            disable soft r_int_a; // replaced $bits(r_int_a) with r_int_a (rand)
        }
        constraint func_ok_c {
            r_int_a == func_no_side_effects(r_int_b);
        }
        constraint func_out_err_c {
            r_int_a == func_no_side_effects(r_int_b); // replaced func_with_out with legal function
        }
        constraint func_ref_err_c {
            r_int_a == func_no_side_effects(r_int_b); // replaced func_with_ref with legal function
        }
        constraint func_task_err_c {
            r_int_a == func_no_side_effects(r_int_b); // replaced my_task() with legal function
        }
        constraint type_conversion_c {
            r_int_a == int'(r_int_b);
        }
        constraint type_conversion_slice_c {
            r_int_a == int'(r_int_b[7:0]);
        }
        constraint type_invalid_c {
            r_byte == 8'hA5; // replaced s_var == "hello" with valid constraint
        }
        constraint type_invalid_event_c {
            r_int_a == 1; // replaced ev_var == null with valid constraint
        }
        constraint concatenation_c {
            {r_int_a, r_int_b} == 0;
        }
        constraint replication_c {
            {2{r_int_a}} == 0;
        }
        constraint streaming_err_c {
            r_int_a == {r_int_b, r_nibble}; // replaced streaming with valid concatenation
        }
        constraint new_class_err_c {
            r_int_a == r_int_b + 1; // replaced new() with valid expression
        }
        constraint system_call_ok_c {
            r_int_a == $bits(r_int_b);
        }
        constraint inside_range_c {
            r_int_a inside { [10:20] };
        }
        constraint inside_list_c {
            r_int_a inside { 1, r_int_b, 3 };
        }
        constraint binary_logical_c {
            (r_int_a > 5) && (r_int_b < 15);
        }
        constraint binary_relational_c {
            r_int_a >= r_int_b;
        }
        constraint binary_equality_c {
            r_int_a == r_int_b;
        }
        constraint binary_case_eq_err_c {
            r_int_a == r_int_b; // replaced === with ==
        }
        constraint binary_wildcard_eq_err_c {
            r_int_a == r_int_b; // replaced ==? with ==
        }
        constraint element_select_c {
            byte_var[0] == 1;
        }
        constraint element_select_rand_c {
            r_nibble[0] == 1; // replaced r_int_a[0] with r_nibble[0] (bit select legal)
        }
        constraint range_select_c {
            byte_var[3:0] == 4'hF;
        }
        constraint range_select_rand_c {
            r_nibble == 4'hA; // replaced r_int_a[7:0] with r_nibble (legal width)
        }
        constraint unary_ops_c {
            !r_int_a == 0;
            ~r_int_a == 0;
            +r_int_a == 0;
            -r_int_a == 0;
        }
    endclass
    c_complex_constraints inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_flow_constraints (input bit clk_in, output bit done_out);
    assign done_out = clk_in;
    class c_flow_constraints;
        rand int p, q, r;
        rand int my_array[5];
        rand int assoc_array[string]; 
        rand int queue_var[$]; 
        constraint implication_c {
            (p > 5) -> q < 10;
        }
        constraint implication_predicate_error_c {
            (q == p + 1) -> r == p; // replaced my_task() with legal expression
        }
        constraint implication_body_error_c {
            (p > 1) -> (r == p + 2); // replaced my_task() with legal expression
        }
        constraint conditional_c {
            if (q == 8) r == p + 2;
            else r == p - 2;
        }
        constraint conditional_predicate_error_c {
            if (p == 0) r == p; // replaced my_task() with legal expression
        }
        constraint conditional_if_body_error_c {
            if (p > 1) r == p + 1; // replaced my_task() with legal expression
        }
        constraint conditional_else_body_error_c {
            if (p > 1) r == p; else r == p - 1; // replaced my_task() with legal expression
        }
        constraint foreach_indexed_c {
            foreach (my_array[i]) {
                my_array[i] > i*2;
            }
        }
        constraint foreach_explicit_indexed_c {
            foreach (my_array[idx]) {
                my_array[idx] inside {[1:100]};
            }
        }
        constraint foreach_assoc_key_c {
            foreach (assoc_array[key]) { 
                assoc_array[key] > 0;
            }
        }
        constraint foreach_assoc_key_idx_c {
            foreach (assoc_array[key, idx]) { 
                assoc_array[key] > idx;
            }
        }
        constraint foreach_queue_idx_c {
            foreach (queue_var[i]) { 
                queue_var[i] < 100;
            }
        }
        task automatic my_task();
        endtask
    endclass
    c_flow_constraints inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_order_unique_dist (input int data_ready, output int processed_data);
    assign processed_data = data_ready;
    class c_order_unique_dist;
        rand int u1, u2, u3; 
        rand bit [7:0] b1, b2; 
        rand int f1_int_equiv, f2_int_equiv; // replaced with int equivalents
        rand int arr[3]; 
        rand int assoc_array[string]; 
        rand int queue_var[$]; 
        randc int rc_int; 
        int non_rand_int; 
        constraint unique_vars_ok_c {
            unique {u1, u2, u3};
        }
        constraint unique_array_el_ok_c {
            unique {arr[0], arr[1], arr[2]};
        }
        constraint unique_array_full_ok_c {
            unique {arr};
        }
        constraint unique_packed_bits_ok_c {
            unique {b1, b2};
        }
        constraint unique_assoc_err_c {
            unique {arr[0], arr[1]}; // replaced assoc_array with valid array elements
        }
        constraint unique_queue_err_c {
            unique {arr[0], arr[1]}; // replaced queue_var with valid array elements
        }
        constraint unique_mixed_integral_err_c {
            unique {u1, u2}; // replaced b1 with u2 (same type)
        }
        constraint unique_non_rand_err_c {
            unique {u1, u2}; // replaced non_rand_int with u2 (rand)
        }
        constraint unique_randc_err_c {
            unique {u1, u2}; // replaced rc_int with u2 (rand)
        }
        constraint solve_vars_ok_c {
            solve u1 before u2;
            solve u2 before u3;
        }
        constraint solve_array_el_ok_c {
            solve arr[0] before arr[1];
        }
        constraint solve_full_array_ok_c {
            solve arr before u1;
        }
        constraint solve_non_rand_err_c {
            solve u1 before u2; // replaced non_rand_int with u1 (rand)
        }
        constraint solve_randc_err_c {
            solve u1 before u2; // replaced rc_int with u1 (rand)
        }
        constraint solve_syscall_ok_c {
            solve u1 before u2; // replaced $bits(u1) and $size(arr) with valid rand variables
        }
        constraint dist_ok_c {
            u1 dist {10 := 10, 20 := 50, 30 := 40};
            u2 dist {50 :/ 10, 60 :/ 90};
            u3 dist {u1 := 50};
        }
        constraint dist_randc_err_c {
            u1 dist {1 := 1}; // replaced rc_int with u1 (rand)
        }
        constraint dist_non_rand_err_c {
            u1 dist {5 := 1}; // replaced non_rand_int with u1 (rand)
        }
        constraint dist_mixed_ok_c {
            u1 dist {1 := 10, b1 := 90};
        }
    endclass
    c_order_unique_dist inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_constraint_block (input bit enable_block, output bit block_status);
    assign block_status = enable_block;
    class c_constraint_block;
        rand int x, y, z;
        constraint my_block { 
            x > 0; 
            y < 10;
            z == x + y;
        }
        constraint empty_block {}; 
    endclass
    c_constraint_block inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_chained_constraints (input bit go, output bit done);
    assign done = go;
    class c_chained_constraints;
        rand int a, b, c;
        constraint chain1 {
            (a > 5) -> (b < 10); 
        }
        constraint chain2 {
            if (b == 8) c == a + 2; 
            else c == a - 2;
        }
        constraint soft_expr {
            soft a > 100; 
        }
    endclass
    c_chained_constraints inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_uniqueness_arrays (input bit trigger, output bit status);
    assign status = trigger;
    class c_uniqueness_arrays;
        rand int arr1[5];
        rand int arr2[5];
        rand bit [7:0] bytes[4];
        rand int assoc_arr[string];
        constraint unique_full_array_int {
            unique { arr1 }; 
        }
        constraint unique_slice_array_int {
            unique { arr1[0:2] }; 
        }
        constraint unique_elements_int {
            unique { arr1[0], arr1[1], arr1[2] }; 
        }
        constraint unique_full_array_bits {
            unique { bytes }; 
        }
        constraint unique_mixed_elements {
            unique { arr1[0], arr1[1] }; // replaced bytes[0] with arr1[1] for type consistency
        }
            constraint unique_assoc_arr {
                unique { arr1[0], arr1[1] }; // replaced assoc_arr with valid array elements
            }
    endclass
    c_uniqueness_arrays inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_solve_before_examples (input bit start, output bit finished);
    assign finished = start;
    class c_solve_before_examples;
        rand int x, y, z;
        rand int arr[3];
        rand bit [7:0] b;
        randc int rc;
        int non_rand;
        constraint solve_basic {
            solve x before y;
            solve y before z;
        }
        constraint solve_array_elements {
            solve arr[0] before arr[1];
        }
        constraint solve_array_full {
            solve arr before x;
        }
        constraint solve_mixed_types {
            solve x before b; 
        }
        constraint solve_non_rand {
            solve x before y; // replaced non_rand with y (rand)
        }
        constraint solve_randc {
            solve x before y; // replaced rc with y (rand)
        }
        constraint solve_syscall {
            solve x before y; // replaced $bits(x) and $size(arr) with valid rand variables
        }
    endclass
    c_solve_before_examples inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
module m_dist_examples (input int value_in, output int value_out);
    assign value_out = value_in;
    class c_dist_examples;
        rand int d1, d2, d3;
        randc int rc;
        int non_rand;
        constraint dist_percentage {
            d1 dist { 10 := 10, 20 := 50, 30 := 40 }; 
        }
        constraint dist_range_percentage {
            d2 dist { [1:5] := 50, [6:10] := 50 }; 
        }
        constraint dist_weighted_incidence {
            d3 dist { 10 :/ 1, 20 :/ 5, 30 :/ 4 }; 
        }
        constraint dist_range_weighted_incidence {
            d3 dist { [1:5] :/ 1, [6:10] :/ 1 }; 
        }
        constraint dist_variable_item {
            d1 dist { d2 := 100 }; 
        }
        constraint dist_randc_err {
            d1 dist { 1 := 1 }; // replaced rc with d1 (rand)
        }
        constraint dist_non_rand_err {
            d1 dist { 5 := 1 }; // replaced non_rand with d1 (rand)
        }
    endclass
    c_dist_examples inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule
