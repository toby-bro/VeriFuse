module CoverageHelper(
    input bit in_h,
    output logic out_h
);
    assign out_h = in_h;
endmodule
module CoverageModule_Control(
    input bit enable,
    input int control_cmd_in,
    input int control_arg1_in,
    input int control_arg2_in,
    input string control_str_in,
    output int control_ret_out
);
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_control(control_cmd_in, control_arg1_in, control_arg2_in, control_str_in);
        end
        control_ret_out = ret_val;
    end
endmodule
module CoverageModule_GetMax(
    input bit enable,
    input int getmax_arg1_in,
    input int getmax_arg2_in,
    input bit helper_in,
    output int getmax_ret_out,
    output logic helper_out
);
    CoverageHelper inst_helper (.in_h(helper_in), .out_h(helper_out));
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_get_max(getmax_arg1_in, getmax_arg2_in, inst_helper);
        end
        getmax_ret_out = ret_val;
    end
endmodule
module CoverageModule_Get(
    input bit enable,
    input int get_arg1_in,
    input int get_arg2_in,
    input bit helper_in,
    output int get_ret_out,
    output logic helper_out
);
    CoverageHelper inst_helper (.in_h(helper_in), .out_h(helper_out));
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_get(get_arg1_in, get_arg2_in, inst_helper);
        end
        get_ret_out = ret_val;
    end
endmodule
module DummyHierModule(
    input bit in_bit,
    output logic out_logic
);
    assign out_logic = in_bit;
endmodule
module CoverageModule_GetHierName(
    input bit enable,
    input int gethier_arg1_in,
    input int gethier_arg2_in,
    input bit dummy_in_to_hier,
    output int gethier_ret_out,
    output logic hier_out
);
    DummyHierModule inst_dummy (
        .in_bit(dummy_in_to_hier),
        .out_logic(hier_out)
    );
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_get(gethier_arg1_in, gethier_arg2_in, inst_dummy);
        end
        gethier_ret_out = ret_val;
    end
endmodule
module CoverageModule_MergeSave(
    input bit enable,
    input int merge_opt_in,
    input string merge_file_in,
    input int save_opt_in,
    input string save_file_in,
    output int merge_ret_out,
    output int save_ret_out
);
    int merge_ret_val;
    int save_ret_val;
    always_comb begin
        merge_ret_val = 0;
        save_ret_val = 0;
        if (enable) begin
            merge_ret_val = $coverage_merge(merge_opt_in, merge_file_in);
            save_ret_val = $coverage_save(save_opt_in, save_file_in);
        end
        merge_ret_out = merge_ret_val;
        save_ret_out = save_ret_val;
    end
endmodule
module CoverageModule_GetCoverage(
    input bit enable,
    output real getcov_ret_out
);
    real ret_val;
    always_comb begin
        ret_val = 0.0;
        if (enable) begin
            ret_val = $get_coverage();
        end
        getcov_ret_out = ret_val;
    end
endmodule
module CoverageModule_SetLoadDB(
    input bit enable,
    input string setdb_name_in,
    input string loaddb_name_in,
    output bit dummy_out
);
    always_comb begin
        if (enable) begin
            $set_coverage_db_name(setdb_name_in);
            $load_coverage_db(loaddb_name_in);
        end
        dummy_out = enable;
    end
endmodule
module CoverageModule_Control_ValidExtra(
    input bit enable,
    input int control_cmd_in,
    input int control_arg1_in,
    input int control_arg2_in,
    input string control_str_in,
    input int extra_arg,
    output int control_ret_out
);
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_control(control_cmd_in, control_arg1_in, control_arg2_in, control_str_in);
        end
        control_ret_out = ret_val;
    end
endmodule
module CoverageModule_GetMax_ValidThirdArg(
    input bit enable,
    input int getmax_arg1_in,
    input int getmax_arg2_in,
    input bit helper_in,
    input string getmax_str_in,
    output int getmax_ret_out,
    output logic helper_out
);
    CoverageHelper inst_helper (.in_h(helper_in), .out_h(helper_out));
    int ret_val;
    always_comb begin
        ret_val = 0;
        if (enable) begin
            ret_val = $coverage_get_max(getmax_arg1_in, getmax_arg2_in, inst_helper);
        end
        getmax_ret_out = ret_val;
    end
endmodule
