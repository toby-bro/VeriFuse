module m_flow_constraints (
    input bit clk_in,
    output bit done_out
);
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
            (q == p + 1) -> r == p; 
        }
        constraint implication_body_error_c {
            (p > 1) -> (r == p + 2); 
        }
        constraint conditional_c {
            if (q == 8) r == p + 2;
            else r == p - 2;
        }
        constraint conditional_predicate_error_c {
            if (p == 0) r == p; 
        }
        constraint conditional_if_body_error_c {
            if (p > 1) r == p + 1; 
        }
        constraint conditional_else_body_error_c {
            if (p > 1) r == p; else r == p - 1; 
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

