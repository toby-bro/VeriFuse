// top module
module top #(parameter GGGp = 8) (
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
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);

    task automatic GGGtask_modify_ref;
        input logic [7:0] GGGinput_val;
        ref logic [7:0] GGGref_var; // Reference argument
        //INJECT
        GGGref_var = GGGinput_val + GGGref_var;
    endtask

    logic [7:0] GGGdata_var = 8'hAA;

    always_comb begin
        // Call site: GGGtask_modify_ref(GGGin, GGGdata_var);
        GGGtask_modify_ref(GGGin, GGGdata_var); // Direct call in always_comb
        //INJECT
        GGGout = GGGdata_var; // GGGdata_var is modified by the task
    end

endmodule

// Module targeting DPI import declarations
module GGGdpi_import_module (
    input logic [31:0] GGGin,
    output logic [31:0] GGGout
);

    import "DPI-C" function int GGGimported_func(input int GGGdpi_arg);
    import "DPI-C" context function int GGGimported_context_func(input int GGGdpi_arg_ctx);

    always_comb begin
        int GGGfunc_result;
        int GGGcontext_result;
        //INJECT
        GGGfunc_result = GGGimported_func(GGGin);
        GGGcontext_result = GGGimported_context_func(GGGin + 1);
        GGGout = GGGfunc_result + GGGcontext_result;
        //INJECT
    end

endmodule

// Module targeting DPI export declarations and definitions
module GGGdpi_export_module (
    input logic [63:0] GGGin,
    output logic [63:0] GGGout
);

    // DPI Export Declarations (visible to C)
    export "DPI-C" task GGGexported_task;
    // Corrected syntax based on lint error: context keyword after routine type for export
    export "DPI-C" task GGGexported_context_task;
    export "DPI-C" function GGGexported_func;

    // SystemVerilog definition of exported routines
    task GGGexported_task;
        input logic [63:0] GGGtask_arg;
        //INJECT
        // Logic for exported task (avoiding simulation tasks or direct output modification)
    endtask

    task GGGexported_context_task;
        input logic [63:0] GGGtask_arg_ctx;
        //INJECT
        // Logic for exported context task (avoiding simulation tasks or direct output modification)
    endtask

    function automatic longint GGGexported_func; // Return type must match export, argument type should match export/usage
        input longint GGGfunc_arg;
        //INJECT
        // Logic for exported function (avoiding simulation tasks)
        return GGGfunc_arg + 1;
    endfunction

    // Add a simple assignment to the output port to satisfy linting,
    // as exported tasks/functions don't typically drive module outputs directly.
    assign GGGout = GGGin;
    //INJECT

endmodule

// Module targeting DPI with unpacked arrays
module GGGdpi_unpacked_array_module (
    input logic [1:0] GGGin [3], // Unpacked array input
    output logic [1:0] GGGout [3] // Unpacked array output
);

    import "DPI-C" function void GGGdpi_array_task(input logic [1:0] GGGarray_in [3], output logic [1:0] GGGarray_out [3]);

    always_comb begin
        //INJECT
        GGGdpi_array_task(GGGin, GGGout);
        //INJECT
    end

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
