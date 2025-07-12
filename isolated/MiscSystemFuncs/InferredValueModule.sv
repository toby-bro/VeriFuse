module InferredValueModule (
    input bit check_sig_in,
    input bit clk_in,
    input bit disable_sig_in,
    output bit prop_explicit_success_out,
    output bit prop_inferred_success_out
);
    property check_inferred_defaults_prop;
        @(posedge clk_in) disable iff (disable_sig_in) check_sig_in |-> 1;
    endproperty
    property check_explicit_prop;
        @(posedge clk_in) disable iff (disable_sig_in) check_sig_in |-> 1;
    endproperty
    assert property (check_inferred_defaults_prop);
    assert property (check_explicit_prop);
    always_comb begin
        prop_inferred_success_out = check_sig_in && disable_sig_in;
        prop_explicit_success_out = check_sig_in || disable_sig_in;
    end
endmodule

