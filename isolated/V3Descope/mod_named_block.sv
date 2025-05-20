module mod_named_block (
    output logic o_done,
    input logic i_start
);
    logic top_level_sig;
      my_scope_a: begin
    logic block_sig_a;
    always_comb begin
      top_level_sig = i_start;
      block_sig_a = top_level_sig;
    end
      end : my_scope_a
      my_scope_b: begin
    logic block_sig_b;
    always_comb begin
       block_sig_b = my_scope_a.block_sig_a;
       o_done = block_sig_b;
    end
      end : my_scope_b
endmodule

