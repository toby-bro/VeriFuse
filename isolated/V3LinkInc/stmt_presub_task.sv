module stmt_presub_task (
    input logic [7:0] in_val_m4,
    output logic [7:0] var_out_m4
);
    logic [7:0] var_m4;
    task automatic update_var_m4(inout logic [7:0] val);
        --val;
    endtask
    always_comb begin
        var_m4 = in_val_m4;
        update_var_m4(var_m4);
        var_out_m4 = var_m4;
    end
endmodule

