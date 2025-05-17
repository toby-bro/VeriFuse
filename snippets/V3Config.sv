module mod_basic (
    input wire i_clk,
    output logic o_done
);
    logic r_state;
    parameter int PARAM_BASIC = 42;
    always_ff @(posedge i_clk) begin
        r_state <= ~r_state;
    end
    always_comb begin
        o_done = r_state;
    end
endmodule
module mod_ftask_attrs (
    input wire i_clk,
    input wire i_start,
    output logic o_result
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
module mod_case_block_attrs (
    input wire [1:0] i_sel,
    input wire [3:0] i_val,
    output logic [3:0] o_out
);
    logic [3:0] l_temp;
    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (i_sel)
            2'b00: l_temp = i_val;
            2'b01: l_temp = i_val << 1;
            2'b10: l_temp = i_val >> 1;
            default: l_temp = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            o_out = l_temp;
        end
    end
endmodule
(* verilator inline *)
(* verilator public_module *)
(* verilator hier_params *)
module mod_module_attrs # (
    parameter int WIDTH = 8
) (
    input wire [WIDTH-1:0] i_in,
    output logic [WIDTH-1:0] o_out
);
    logic [WIDTH-1:0] r_data;
    always_comb begin
        r_data = i_in;
    end
    assign o_out = r_data;
endmodule
(* verilator no_inline *)
module mod_no_inline_module (
    input wire i_go,
    output logic o_done_ni
);
    logic r_toggle = 1'b0;
    always_ff @(posedge i_go) begin
        r_toggle <= ~r_toggle;
    end
    assign o_done_ni = r_toggle;
endmodule
module mod_lint_target (
    input wire i_a,
    input wire i_b,
    output logic o_sum
);
    logic l_reg;
    logic [7:0] wide_reg;
    always_comb begin
        l_reg = 1;
        wide_reg = {i_a, i_b};
    end
    assign o_sum = i_a + i_b;
endmodule
