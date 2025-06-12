module stmt_postadd_task (
    input logic [7:0] in_val_m3,
    output logic [7:0] var_out_m3
);
    logic [7:0] var_m3;
    task automatic update_var_m3(inout logic [7:0] val);
        val++;
    endtask
    always_comb begin
        var_m3 = in_val_m3;
        update_var_m3(var_m3);
        var_out_m3 = var_m3;
    end
endmodule

