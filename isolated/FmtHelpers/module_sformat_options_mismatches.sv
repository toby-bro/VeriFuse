module module_sformat_options_mismatches (
    input real in_real,
    input int in_val,
    input bit trigger_diagnostics,
    output bit out_status,
    output string s_diag_mismatch,
    output string s_options
);
    bit status = 1'b1;
    typedef struct {
        bit [2:0] f1;
        shortint f2;
    } local_struct_t;
    local_struct_t local_struct_var;
    typedef union {
        int i;
        logic [15:0] l;
    } local_union_t;
    local_union_t local_union_var;
    always_comb begin
        s_options = $sformatf("Options: %08d %d %5h %8x %.2f %08.3e", in_val, in_val, in_val, in_val, in_real, in_real);
    end
    always_comb begin
        s_diag_mismatch = "";
        s_diag_mismatch = $sformatf("Type mismatch: %s", in_val);
        if (trigger_diagnostics) begin
            local_struct_var = '{f1: 3'b110, f2: 1234};
            local_union_var.i = 98765;
        end
    end
    assign out_status = status;
endmodule

