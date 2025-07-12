module VariableLifetimeAndProceduralBlocks (
    input wire clk,
    input wire [7:0] data_in,
    input wire edge_sig,
    input wire rst,
    output logic [7:0] data_out_comb,
    output logic [7:0] data_out_ff,
    output logic out_toggle_always,
    output logic out_toggle_edge,
    output int static_count_out
);
    static integer static_counter = 0;
    logic [7:0] ff_reg_data;
    logic [7:0] latch_reg_data;
    static logic explicit_static_var = 1'b0;
    final begin end
    always_comb begin
        data_out_comb = ff_reg_data + 1;
    end
    always_ff @(posedge clk or negedge rst) begin
        automatic int auto_ff_var = 5;
        if (!rst) begin
            ff_reg_data       <= 8'h00;
            static_counter    = 0;
            out_toggle_always <= 1'b0;
        end
        else begin
            ff_reg_data       <= data_in + auto_ff_var;
            static_counter    = static_counter + 1;
            out_toggle_always <= ~out_toggle_always;
        end
        data_out_ff      <= ff_reg_data;
        static_count_out <= static_counter;
    end
    always_latch begin
        automatic int auto_latch_var = 3;
        if (data_in > 10)
            latch_reg_data = data_in + auto_latch_var;
    end
    always @(posedge edge_sig or negedge edge_sig) begin
        automatic int auto_edge_var = 2;
        out_toggle_edge  <= ~out_toggle_edge;
    end
    task automatic my_task_auto(input int count, ref logic [7:0] data);
        automatic int task_local_var;
        task_local_var = count * 2;
        data           = data + task_local_var;
    endtask
    function automatic int my_func_auto(input int count);
        automatic int func_local_var;
        func_local_var = count * 3;
        return func_local_var;
    endfunction
endmodule

