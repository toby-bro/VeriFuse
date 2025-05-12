// top module
module topoi #(parameter GGGp = 8) (
    input logic [GGGp-1:0] GGGin,
    output logic [GGGp-1:0] GGGout
);

    logic [GGGp-1:0] GGGtemp_var = GGGin;

    always_comb begin
        //INJECT
        GGGout = GGGtemp_var;
    end

endmodule

// Module targeting simple tasks
module GGGsimple_task_module #(parameter GGGp_mod = 4) (
    input logic [GGGp_mod-1:0] GGGin,
    output logic [GGGp_mod-1:0] GGGout
);

    logic [GGGp_mod-1:0] GGGinternal_reg;

    task automatic GGGsimple_task;
        input logic [GGGp_mod-1:0] GGGtask_in;
        output logic [GGGp_mod-1:0] GGGtask_out;
        //INJECT
        GGGtask_out = GGGtask_in + 1;
    endtask

    always_comb begin
        // This is where a task call site could be processed by V3Task.cpp
        // Example call: GGGsimple_task(GGGin, GGGinternal_reg);
        GGGinternal_reg = GGGin + 2; // Placeholder logic
        //INJECT
        GGGout = GGGinternal_reg;
    end

endmodule

// Module targeting simple functions
module GGGsimple_function_module #(parameter GGGp_func = 16) (
    input logic [GGGp_func-1:0] GGGin,
    output logic [GGGp_func-1:0] GGGout
);

    function automatic logic [GGGp_func-1:0] GGGsimple_func;
        input logic [GGGp_func-1:0] GGGfunc_in;
        logic [GGGp_func-1:0] GGGfunc_local_var;
        //INJECT
        GGGfunc_local_var = GGGfunc_in * 2;
        return GGGfunc_local_var;
    endfunction

    assign GGGout = GGGsimple_func(GGGin); // Function call site
    //INJECT

endmodule

// Module targeting tasks with default/named arguments
module GGGtask_default_named_args (
    input logic GGGin,
    output logic GGGout
);

    parameter int GGGparam1 = 10;

    task automatic GGGtask_with_defaults;
        input int GGGarg1 = GGGparam1;
        input int GGGarg2 = 20;
        output logic GGGtask_status;
        //INJECT
        if (GGGarg1 > GGGarg2) begin
            GGGtask_status = 1;
        end else begin
            GGGtask_status = 0;
        end
    endtask

    logic GGGstatus_var;

    always_comb begin
        // Call site examples that could be processed by V3Task.cpp:
        // GGGtask_with_defaults(.GGGarg2(30), .GGGtask_status(GGGstatus_var)); // Named args
        // GGGtask_with_defaults(.GGGtask_status(GGGstatus_var)); // Using both defaults
        // GGGtask_with_defaults(15, 25, GGGstatus_var); // Positional
        GGGstatus_var = GGGin; // Placeholder logic, doesn't actually call the task in this simplified example
        //INJECT
        GGGout = GGGstatus_var;
    end

endmodule

// Module targeting tasks with ref arguments
module GGGtask_ref_args (
    input logic clk,            // Clock input
    input logic rst_n,          // Asynchronous active-low reset
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);

    task automatic GGGtask_modify_ref;
        input logic [7:0] GGGinput_val;
        ref logic [7:0] GGGref_var; // Reference argument
        //INJECT
        GGGref_var = GGGinput_val + GGGref_var;
    endtask

    logic [7:0] GGGdata_var; // Removed initializer, will be set by reset
    logic [7:0] GGGdata_var_next;

    // Combinational logic to calculate the next state of GGGdata_var
    always_comb begin
        GGGdata_var_next = GGGdata_var; // Start with current value
        GGGtask_modify_ref(GGGin, GGGdata_var_next); // Task modifies GGGdata_var_next
    end

    // Sequential logic to register GGGdata_var
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            GGGdata_var <= 8'hAA; // Initialize GGGdata_var on reset
        end else begin
            GGGdata_var <= GGGdata_var_next;
        end
    end

    // Assign output based on the registered GGGdata_var
    assign GGGout = GGGdata_var;

endmodule


// Module demonstrating pragma handling by V3Task
module GGGtask_pragma_no_inline (
    input logic GGGin,
    output logic GGGout
);

    task GGGtask_cannot_inline;
        // verilator no_inline_task
        //INJECT
        // Placeholder logic
    endtask

    always_comb begin
        // Call site: GGGtask_cannot_inline();
        // Since it's a task, it would typically be in a procedural block
        // For this example, just show the declaration and a dummy assignment
        GGGout = GGGin;
        //INJECT
    end

endmodule


// Module targeting tasks with control flow
module GGGtask_with_control_flow (
    input int GGGin,
    output int GGGout
);

    task automatic GGGconditional_task;
        input int GGGtask_in_cond;
        output int GGGtask_out_cond;
        int GGGlocal_counter = 0;
        //INJECT
        while (GGGlocal_counter < 5) begin
            GGGlocal_counter++;
            //INJECT
        end
        if (GGGtask_in_cond > 10) begin
            GGGtask_out_cond = GGGlocal_counter;
        end else begin
            GGGtask_out_cond = GGGtask_in_cond;
        end
    endtask

    int GGGresult_var;

    always_comb begin
        // Call site: GGGconditional_task(GGGin, GGGresult_var);
        GGGconditional_task(GGGin, GGGresult_var); // Direct call in always_comb
        //INJECT
        GGGout = GGGresult_var;
    end

endmodule
