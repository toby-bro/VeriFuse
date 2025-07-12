module m_complex_constraints (
    input bit start_trigger,
    output bit done_flag
);
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
            soft r_int_b == 5; 
        }
        constraint disable_soft_ok_c {
            disable soft r_int_a;
        }
        constraint disable_soft_non_rand_err_c {
            disable soft r_int_b; 
        }
        constraint disable_soft_randc_err_c {
            disable soft r_int_a; 
        }
        constraint disable_soft_syscall_ok_c {
            disable soft r_int_a; 
        }
        constraint func_ok_c {
            r_int_a == func_no_side_effects(r_int_b);
        }
        constraint func_out_err_c {
            r_int_a == func_no_side_effects(r_int_b); 
        }
        constraint func_ref_err_c {
            r_int_a == func_no_side_effects(r_int_b); 
        }
        constraint func_task_err_c {
            r_int_a == func_no_side_effects(r_int_b); 
        }
        constraint type_conversion_c {
            r_int_a == int'(r_int_b);
        }
        constraint type_conversion_slice_c {
            r_int_a == int'(r_int_b[7:0]);
        }
        constraint type_invalid_c {
            r_byte == 8'hA5; 
        }
        constraint type_invalid_event_c {
            r_int_a == 1; 
        }
        constraint concatenation_c {
            {r_int_a, r_int_b} == 0;
        }
        constraint replication_c {
            {2{r_int_a}} == 0;
        }
        constraint streaming_err_c {
            r_int_a == {r_int_b, r_nibble}; 
        }
        constraint new_class_err_c {
            r_int_a == r_int_b + 1; 
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
            r_int_a == r_int_b; 
        }
        constraint binary_wildcard_eq_err_c {
            r_int_a == r_int_b; 
        }
        constraint element_select_c {
            byte_var[0] == 1;
        }
        constraint element_select_rand_c {
            r_nibble[0] == 1; 
        }
        constraint range_select_c {
            byte_var[3:0] == 4'hF;
        }
        constraint range_select_rand_c {
            r_nibble == 4'hA; 
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

