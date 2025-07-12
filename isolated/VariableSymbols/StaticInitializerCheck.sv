module StaticInitializerCheck (
    input wire [7:0] in_net,
    input logic [7:0] in_var,
    output logic [7:0] out_val
);
    static logic [7:0] static_var_a                 = 8'h10;
    static logic [7:0] static_var_b                 = static_var_a + 1;
    static logic [7:0] static_var_c                 = 8'h20;
    static logic [7:0] static_var_d                 = static_var_c + 1;
    static logic [7:0] static_var_ref_input_diag    = in_var + 1;
    static logic [7:0] static_var_ref_net_diag      = in_net + 1;
    static logic [7:0] static_var_ref_func          = get_static_val() + 1;
    static logic [7:0] static_var_ref_sys           = $bits(in_var) + 1;
    static logic [7:0] static_var_e                 = 8'h30;
    static logic [7:0] static_var_ref_after_diag    = static_var_e + 1;
    always_comb begin
        out_val = static_var_b               +
            static_var_d               +
            static_var_ref_func        +
            static_var_ref_sys         +
            static_var_ref_input_diag  +
            static_var_ref_net_diag    +
            static_var_ref_after_diag  +
            static_var_e;
    end
    function automatic logic [7:0] get_static_val();
        return static_var_a * 2;
    endfunction
endmodule

