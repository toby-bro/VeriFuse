module param_defaults #(
    parameter int BASE_OFFSET = 7,
    parameter int DERIVED_VALUE = (BASE_OFFSET + 10) * SCALE_FACTOR,
    parameter int SCALE_FACTOR = 3
) (
    input logic [1:0] i_select,
    output int o_selected_val
);
    parameter int OptionValues [3] = '{BASE_OFFSET, SCALE_FACTOR, DERIVED_VALUE};
    always_comb begin
        case (i_select)
            0: o_selected_val = OptionValues[0];
            1: o_selected_val = OptionValues[1];
            2: o_selected_val = OptionValues[2];
            default: o_selected_val = 0;
        endcase
    end
endmodule

