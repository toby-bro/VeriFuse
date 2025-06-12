module mod_var_attrs (
    input wire [7:0] i_data,
    output logic [7:0] o_data
);
    (* verilator public *)
    logic [7:0] r_internal_pub;
    (* verilator forceable *)
    logic [7:0] r_internal_force;
    (* verilator isolate_assignments *)
    logic r_isolate_me;
    (* verilator public_flat_rw *)
    logic [7:0] r_flat_rw;
    always_comb begin
        r_flat_rw = i_data + 1;
    end
    always_comb begin
        r_internal_pub = i_data;
        r_internal_force = r_internal_pub;
        r_isolate_me = |i_data;
        o_data = r_internal_force;
    end
    task modify_vars (input bit en);
        (* verilator public *)
        logic [3:0] task_local_pub;
        if (en) begin
            task_local_pub = i_data[3:0];
        end
    endtask
endmodule

