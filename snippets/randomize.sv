typedef struct packed {
    rand logic [7:0] GGG_field1;
    rand int unsigned GGG_field2;
    // INJECT - Struct body
} GGG_my_struct_t;

// Class to contain rand variable for 'top' module
class GGG_TopRandContainer #(parameter GGG_CONTAINER_WIDTH = 8);
    rand logic [GGG_CONTAINER_WIDTH-1:0] GGG_rand_var;
    // INJECT - Top container class body
endclass

// Class to contain randc variable
class GGG_RandcContainer #(parameter GGG_CONTAINER_WIDTH = 4);
    randc logic [GGG_CONTAINER_WIDTH-1:0] GGG_randc_var;
    // INJECT - Randc container class body
endclass

// Class to contain structured rand variable
class GGG_StructRandContainer;
    rand GGG_my_struct_t GGG_struct_var;
    // INJECT - Struct rand container class body
endclass

// Class to contain aggregate (array) rand variable
class GGG_ArrayRandContainer #(parameter GGG_CONTAINER_SIZE = 4);
    rand logic [7:0] GGG_array_var [GGG_CONTAINER_SIZE]; // Unpacked array
    // INJECT - Array rand container class body
endclass

// Class to contain rand variable and simple constraint
class GGG_SimpleConstraintContainer #(parameter GGG_CONTAINER_WIDTH = 16);
    rand logic [GGG_CONTAINER_WIDTH-1:0] GGG_rand_var;
    // Use a class parameter or local variable if constraint needs dynamic bounds
    parameter GGG_CONSTRAINT_MAX = GGG_CONTAINER_WIDTH * 2;

    constraint GGG_simple_constr {
        GGG_rand_var > 1; // Simple lower bound
        //INJECT - Simple constraint body
        GGG_rand_var < GGG_CONSTRAINT_MAX; // Refers to class parameter
    }
    // INJECT - Simple constraint container class body
endclass

// Class to contain rand variables and constraint with 'if'
class GGG_ConstraintIfContainer;
    rand int GGG_rand_var1;
    rand int GGG_rand_var2;
    bit GGG_condition_var; // Member to control constraint branch

    // Constraint with if
    constraint GGG_if_constr {
        if (GGG_condition_var) {
            GGG_rand_var1 < GGG_rand_var2;
            //INJECT - Constraint if body
        } else {
            GGG_rand_var1 == GGG_rand_var2;
        }
        GGG_rand_var1 inside {[-100:100]};
        GGG_rand_var2 inside {[-100:100]};
         //INJECT - Constraint if end body
    }
    // INJECT - Constraint if container class body
endclass

// Class to contain rand array and constraint with 'foreach'
class GGG_ArrayConstraintContainer #(parameter GGG_CONTAINER_SIZE = 3);
    rand logic [7:0] GGG_array_var [GGG_CONTAINER_SIZE];
    int GGG_index_limit; // Member to use in constraint expression

    constraint GGG_foreach_constr {
        foreach (GGG_array_var[GGG_idx]) {
            GGG_array_var[GGG_idx] inside {[0:GGG_index_limit*10]}; // Refers to class member
            //INJECT - Constraint foreach body
        }
        //INJECT - Constraint foreach end body
    }
    // INJECT - Array constraint container class body
endclass

// Class to demonstrate rand_mode task
class GGG_RandModeContainer;
    rand int GGG_rand_var1;
    rand int GGG_rand_var2;

    task GGG_set_modes(bit GGG_mode_val);
        // Test setting mode on a specific variable
        GGG_rand_var1.rand_mode(GGG_mode_val);
        //INJECT - rand_mode task body 1
        // Test setting mode on another variable
        GGG_rand_var2.rand_mode(!GGG_mode_val);
        //INJECT - rand_mode task body 2
    endtask
    // INJECT - Rand mode container class body
endclass

// Class to demonstrate constraint_mode task
class GGG_ConstraintModeContainer;
    rand int GGG_rand_var;

    constraint GGG_my_constraint {
        GGG_rand_var > 10;
        //INJECT - Constraint mode constraint body
    }

    task GGG_control_constraint(bit GGG_mode_val);
        // Test setting mode on a specific constraint
        GGG_my_constraint.constraint_mode(GGG_mode_val);
        //INJECT - constraint_mode task body
    endtask
    // INJECT - Constraint mode container class body
endclass

// Class used within generate blocks
class GGG_GenRandContainer;
    rand int GGG_generated_rand_var;

    constraint GGG_gen_constr {
        GGG_generated_rand_var inside {[0:10]};
         //INJECT - Generate container class constraint
    }
    // INJECT - Generate container class body
endclass

// Existing SimpleClass for GGG_ClassRandModule
class GGG_SimpleClass #(parameter GGG_CLASS_WIDTH = 8);
    rand logic [GGG_CLASS_WIDTH-1:0] GGG_class_rand_var;
    rand int unsigned GGG_class_rand_int;

    // Simple constraint
    constraint GGG_class_constr1 {
        GGG_class_rand_var < 100;
        //INJECT - Simple class constraint
    }

    // Constraint with if
    constraint GGG_class_constr2 {
        if (GGG_class_rand_var > 50) {
            GGG_class_rand_int > 10;
             //INJECT - Class constraint if body
        } else {
            GGG_class_rand_int == 0;
            //INJECT - Class constraint else body
        }
    }

    // Note: The built-in randomize method cannot be redefined.
    // INJECT - Simple class body
endclass

module top #(parameter GGG_WIDTH = 8) (
    input logic [GGG_WIDTH-1:0] GGGin,
    output logic [GGG_WIDTH-1:0] GGGout
);
    // Instantiate the class containing the rand variable
    GGG_TopRandContainer #(GGG_WIDTH) GGG_rand_h = new();

    always_comb begin
        //INJECT
        if (GGG_rand_h != null) begin
             GGGout = GGGin + GGG_rand_h.GGG_rand_var;
        end else begin
             GGGout = GGGin;
        end
        //INJECT
    end
    // INJECT - Top module body
endmodule

module GGG_RandcVarModule #(parameter GGG_WIDTH = 4) (
    input logic GGGin,
    output logic [GGG_WIDTH-1:0] GGGout
);
    // Instantiate the class containing the randc variable
    GGG_RandcContainer #(GGG_WIDTH) GGG_randc_h = new();

    always_comb begin
        //INJECT
        if (GGGin && GGG_randc_h != null) begin
            GGGout = GGG_randc_h.GGG_randc_var;
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Randc module body
endmodule

module GGG_StructuredRandModule (
    input logic [7:0] GGGin,
    output logic [15:0] GGGout
);
    // Instantiate the class containing the structured rand variable
    GGG_StructRandContainer GGG_struct_h = new();

    always_comb begin
        //INJECT
        if (GGG_struct_h != null) begin
            GGGout = {GGG_struct_h.GGG_struct_var.GGG_field1, GGG_struct_h.GGG_struct_var.GGG_field2[7:0]};
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Structured rand module body
endmodule

module GGG_AggregateRandModule #(parameter GGG_SIZE = 4) (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    // Instantiate the class containing the rand array
    GGG_ArrayRandContainer #(GGG_SIZE) GGG_array_h = new();

    always_comb begin
        //INJECT
        if (GGG_array_h != null) begin
            GGGout = GGG_array_h.GGG_array_var[GGGin % GGG_SIZE];
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Aggregate rand module body
endmodule

module GGG_SimpleConstraintModule #(parameter GGG_WIDTH = 16) (
    input logic [GGG_WIDTH-1:0] GGGin,
    output logic [GGG_WIDTH-1:0] GGGout
);
    // Instantiate the class containing the rand variable and constraint
    // Pass module parameter to class parameter if needed
    GGG_SimpleConstraintContainer #(GGG_WIDTH) GGG_constraint_h = new();

    always_comb begin
        //INJECT
        if (GGG_constraint_h != null) begin
            GGGout = GGG_constraint_h.GGG_rand_var;
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Simple constraint module body
endmodule

module GGG_ConstraintIfModule (
    input bit GGGin, // Input used conceptually to influence class member
    output int GGGout
);
    // Instantiate the class containing rand variables and constraint with if
    GGG_ConstraintIfContainer GGG_constraint_h = new();

    // Note: In a real randomized testbench, you'd set GGG_constraint_h.GGG_condition_var = GGGin;
    // before calling randomize() on the class handle. The always_comb just accesses the members.
    always_comb begin
        //INJECT
        if (GGG_constraint_h != null) begin
            GGGout = GGG_constraint_h.GGG_rand_var1 + GGG_constraint_h.GGG_rand_var2;
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Constraint if module body
endmodule

module GGG_ConstraintForeachModule #(parameter GGG_SIZE = 3) (
    input logic [2:0] GGGin, // Input used conceptually for constraint bound
    output logic [7:0] GGGout
);
    // Instantiate the class containing rand array and constraint with foreach
    GGG_ArrayConstraintContainer #(GGG_SIZE) GGG_constraint_h = new();

    // Note: In a real testbench, you'd set GGG_constraint_h.GGG_index_limit = GGGin;
    // before calling randomize().
    always_comb begin
        //INJECT
        if (GGG_constraint_h != null) begin
             GGGout = GGG_constraint_h.GGG_array_var[GGGin % GGG_SIZE];
        end else begin
             GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Constraint foreach module body
endmodule

module GGG_RandModeModule (
    input bit [0:0] GGGin, // Use a single bit for mode control
    output bit GGGout
);
    // Instantiate the class containing rand variables and rand_mode task
    GGG_RandModeContainer GGG_rand_h = new();

    // The GGG_rand_h.GGG_set_modes(GGGin[0]) call would typically happen in procedural code
    // like an initial block or task before a randomize() call. The code below
    // just shows the module structure and access to class members.

    always_comb begin
        // Dummy logic accessing class members
        //INJECT
        if (GGG_rand_h != null) begin
            GGGout = (GGG_rand_h.GGG_rand_var1 > 0) || (GGG_rand_h.GGG_rand_var2 > 0);
        end else begin
            GGGout = 0;
        end
        //INJECT
    end

    // Example task showing where GGG_set_modes might be called (not synthesized/timed)
    task GGG_module_control_modes();
        if (GGG_rand_h != null) begin
            GGG_rand_h.GGG_set_modes(GGGin[0]);
            //INJECT - Module task calling class rand_mode task
        end
    endtask
    // INJECT - Rand mode module body
endmodule

module GGG_ConstraintModeModule (
    input bit GGGin,
    output bit GGGout
);
    // Instantiate the class containing rand variable, constraint, and constraint_mode task
    GGG_ConstraintModeContainer GGG_constraint_h = new();

    // The GGG_constraint_h.GGG_control_constraint(GGGin) call would typically happen
    // in procedural code before randomize().

    always_comb begin
         // Dummy logic accessing class members
         //INJECT
        if (GGG_constraint_h != null) begin
            GGGout = (GGG_constraint_h.GGG_rand_var > 20);
        end else begin
            GGGout = 0;
        end
        //INJECT
    end

    // Example task showing where GGG_control_constraint might be called
    task GGG_module_control_constraints();
        if (GGG_constraint_h != null) begin
            GGG_constraint_h.GGG_control_constraint(GGGin);
            //INJECT - Module task calling class constraint_mode task
        end
    endtask
    // INJECT - Constraint mode module body
endmodule

module GGG_GenerateModule (
    input bit GGGin, // Input used conceptually to influence logic
    output int GGGout
);
    genvar GGG_i;
    // Accumulate sum across instances - note: access from multiple processes is for demonstrating structure
    int GGG_sum_accum = 0;

    for (GGG_i = 0; GGG_i < 2; GGG_i = GGG_i + 1) begin : GGG_gen_block
        // Declare and instantiate the class handle inside the generate block
        // This handle is unique per generate instance
        GGG_GenRandContainer GGG_gen_rand_h = new();

        always_comb begin
            // This block is instantiated per generate iteration.
            // Access the rand variable from this instance.
            // Direct write from multiple comb blocks to a single variable is problematic
            // for synthesis but works for elaboration/linting purposes here to access
            // the generated rand variable.
            // INJECT - always_comb inside generate block
            if (GGG_gen_rand_h != null) begin
                 // Example access - a real design would use specific logic per instance
                 // For demonstrating AST structure, we can access the handle.
                 // Avoid direct write to module variable GGG_sum_accum from here.
                 // Instead, maybe just access the variable value.
                 // The randomization itself happens on the handle before this block runs.
                 // The value of GGG_gen_rand_h.GGG_generated_rand_var is elaborated.
                 // We can perhaps combine the values conceptually in the output logic.
            end
        end
    end

    // Assign output based on GGGin and conceptually elaborated rand values
    // Note: Accessing variables from *inside* generate-for blocks from *outside* is
    // complex and depends on the exact name/scope. A safer way to exercise this
    // is to define signals inside the generate and use them outside.
    // Let's simplify the always_comb block inside the generate and read the
    // output based on a fixed structure.

    // Redo generate to make access simpler for demonstration
    genvar GGG_j;
    logic [7:0] GGG_gen_rand_values[2]; // Array to conceptually hold values

    for (GGG_j = 0; GGG_j < 2; GGG_j = GGG_j + 1) begin : GGG_gen_block_access
        // Declare and instantiate the class handle inside the generate block
        GGG_GenRandContainer GGG_gen_rand_h_j = new();

        // Assign the rand value from the instance's handle to an array element
        // (This is for demonstrating access structure, not typical synthesis)
        always_comb begin
             // INJECT - always_comb inside generate block access
             if (GGG_gen_rand_h_j != null) begin
                 GGG_gen_rand_values[GGG_j] = GGG_gen_rand_h_j.GGG_generated_rand_var[7:0];
             end else begin
                 GGG_gen_rand_values[GGG_j] = 0;
             end
             // INJECT - always_comb inside generate block access end
        end
    end


    // Assign output based on GGGin and the values conceptually collected
    always_comb begin
        // INJECT - always_comb outside generate block
        int GGG_local_sum = 0;
        for (int GGG_k = 0; GGG_k < 2; GGG_k++) begin
            GGG_local_sum = GGG_local_sum + GGG_gen_rand_values[GGG_k];
        end

        if (GGGin) begin
            GGGout = GGG_local_sum;
        end else begin
            GGGout = -GGG_local_sum;
        end
        // INJECT - always_comb outside generate block end
    end
    // INJECT - Generate module body
endmodule


module GGG_ClassRandModule (
    input logic [7:0] GGGin, // Input used conceptually in logic
    output logic [7:0] GGGout
);
    // Declaration and instantiation of a class handle
    GGG_SimpleClass GGG_class_h = new();

    // We cannot call GGG_class_h.randomize() or GGG_class_h.constraint_mode() etc.
    // directly in module-level continuous assignments or always_comb.
    // The C++ code handles parsing these calls wherever they appear in the AST
    // (e.g., initial blocks, tasks, functions, sequences, properties, etc.).
    // The purpose of this module is to have a class defined for V3Randomize to process.

    always_comb begin
        // Dummy logic showing access to rand members via handle
        //INJECT
        if (GGG_class_h != null) begin
            GGGout = GGG_class_h.GGG_class_rand_var + GGGin;
        end else begin
            GGGout = GGGin;
        end
        //INJECT
    end
    // INJECT - Class rand module body
endmodule
