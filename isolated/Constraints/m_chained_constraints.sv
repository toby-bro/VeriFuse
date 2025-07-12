module m_chained_constraints (
    input bit go,
    output bit done
);
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

