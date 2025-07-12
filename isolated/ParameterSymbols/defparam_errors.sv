module defparam_errors #(
    parameter int P_VALID_TARGET = 1000
) (
    input logic i_trigger,
    output int o_valid_param
);
    logic internal_signal;
    defparam P_VALID_TARGET = 1100;
    always_comb begin
        o_valid_param = P_VALID_TARGET;
        internal_signal = i_trigger;
    end
endmodule

