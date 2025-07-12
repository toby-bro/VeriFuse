module basic_lookup (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PARAM = 10;
    logic [7:0] local_var_mb;
    function automatic logic [7:0] add_param(logic [7:0] input_val);
        return input_val + PARAM;
    endfunction
    always_comb begin : named_block_scope
        static logic [7:0] temp_nb;
        temp_nb = add_param(in_val);
        local_var_mb = temp_nb;
    end
    assign out_val = local_var_mb + 1;
endmodule

