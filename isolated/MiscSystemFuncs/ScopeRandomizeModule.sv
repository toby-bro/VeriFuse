class ScopeRandomizable;
    rand int scope_int_non_rand;
    rand logic [7:0] scope_byte_non_rand;
    constraint scope_int_constr { scope_int_non_rand > 10; };
    constraint scope_byte_constr { scope_byte_non_rand != 0; };
endclass

module ScopeRandomizeModule (
    input bit clk,
    input bit trigger_rand_scope,
    output logic [7:0] out_scope_rand_byte,
    output int out_scope_rand_int,
    output bit scope_rand_result
);
    ScopeRandomizable scope_obj = null;
    always_ff @(posedge clk) begin
        if (scope_obj == null) begin
            scope_obj = new();
        end
        if (trigger_rand_scope && scope_obj != null) begin
            scope_rand_result <= scope_obj.randomize();
        end else begin
            scope_rand_result <= 0;
        end
        if (scope_obj != null) begin
            out_scope_rand_int <= scope_obj.scope_int_non_rand;
            out_scope_rand_byte <= scope_obj.scope_byte_non_rand;
        end else begin
            out_scope_rand_int <= 'x;
            out_scope_rand_byte <= 'x;
        end
    end
endmodule

