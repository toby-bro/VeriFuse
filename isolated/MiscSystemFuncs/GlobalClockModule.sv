module GlobalClockModule (
    input bit clk_in,
    input bit enable_prop,
    output bit assertion_eval_out
);
    property check_global_clock_prop;
        @(posedge clk_in) disable iff (!enable_prop) 1;
    endproperty
    assert property (check_global_clock_prop);
    always_comb begin
        assertion_eval_out = enable_prop;
    end
endmodule

