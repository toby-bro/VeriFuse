module m_solve_before_examples (
    input bit start,
    output bit finished
);
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
            solve x before y; 
        }
        constraint solve_randc {
            solve x before y; 
        }
        constraint solve_syscall {
            solve x before y; 
        }
    endclass
    c_solve_before_examples inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule

