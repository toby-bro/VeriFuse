module AssignmentPatterns (
    input logic [15:0] in_val,
    output logic out_pattern_var,
    output logic [23:0] out_repl,
    output logic [7:0] out_struct_a,
    output logic [7:0] out_struct_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } my_struct_t;
    my_struct_t struct_var;
    logic [7:0] repl_array [0:2];
    logic pattern_case_temp;
    always_comb begin
        struct_var     = '{ field_a: in_val[7:0], field_b: in_val[15:8] };
        out_struct_a   = struct_var.field_a;
        out_struct_b   = struct_var.field_b;
        repl_array     = '{ 3 { in_val[7:0] } };
        out_repl       = {repl_array[0], repl_array[1], repl_array[2]};
        case (in_val)
            16'h0000: pattern_case_temp = 1'b0;
            16'h0001: begin
                logic [15:0] pat_var_item = in_val;
                pattern_case_temp = |pat_var_item;
            end
            default: pattern_case_temp = |in_val;
        endcase
        out_pattern_var = pattern_case_temp;
    end
endmodule

