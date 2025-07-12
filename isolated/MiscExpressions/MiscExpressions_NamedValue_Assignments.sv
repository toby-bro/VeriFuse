module MiscExpressions_NamedValue_Assignments (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_const_var_val,
    output logic [7:0] out_enum_val,
    output logic [7:0] out_param_val,
    output logic [15:0] out_sum
);
    parameter int PARAM_VAL = 10;
    localparam logic [7:0] CONST_PARAM = 5;
    const logic [7:0] CONST_VAR = 20;
    logic [7:0] local_var;
    enum { ENUM_VAL1 = 1, ENUM_VAL2 = 2 } enum_type;
    task automatic automatic_task;
        input logic [7:0] arg_a;
        input logic [7:0] arg_b;
        output logic [15:0] sum;
        automatic logic [7:0] auto_local_in_task;
        begin
            auto_local_in_task = arg_b;
            sum = arg_a + auto_local_in_task;
        end
    endtask
    always_comb begin
        logic [15:0] temp_sum;
        local_var = in_a;
        automatic_task(local_var, in_b, temp_sum);
        out_sum = temp_sum;
        out_param_val = PARAM_VAL;
        out_const_var_val = CONST_VAR;
        out_enum_val = ENUM_VAL1;
    end
endmodule

