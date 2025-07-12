module defparam_basic #(
    parameter int P_MOD_PARAM = 500
) (
    input logic i_valid,
    output int o_param_value
);
    defparam P_MOD_PARAM = 750;
    always_comb begin
        o_param_value = P_MOD_PARAM;
    end
endmodule

