module mod_ftask_attrs (
    output logic o_result,
    input wire i_clk,
    input wire i_start
);
    logic r_temp = 1'b0;
    (* verilator public_task *)
    (* verilator no_inline_task *)
    task my_task (input bit enable);
        if (enable) begin
            r_temp <= ~r_temp;
        end
    endtask : my_task
    (* verilator public_func *)
    (* verilator isolate_assignments *)
    function automatic logic my_func (input logic data);
        logic func_local_var;
        func_local_var = data ^ r_temp;
        return func_local_var;
    endfunction : my_func
    always_ff @(posedge i_clk) begin
        my_task(i_start);
    end
    always_comb begin
        o_result = my_func(r_temp);
    end
endmodule

