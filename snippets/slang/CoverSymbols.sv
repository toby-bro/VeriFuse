module covergroup_basic_module (
    input bit basic_in,
    output bit basic_out
);
    covergroup basic_cg @(basic_in);
        cp_basic: coverpoint basic_in {
            bins basic_bins = {0, 1};
        }
    endgroup
    basic_cg basic_cg_inst;
    always_comb begin
        if (basic_cg_inst == null) basic_cg_inst = new();
        basic_cg_inst.sample();
        basic_out = basic_in;
    end
endmodule
module covergroup_options_module (
    input int opt_value_1,
    input logic [1:0] opt_value_2,
    output int opt_out
);
    covergroup options_cg @(opt_value_1 or opt_value_2);
        type_option.weight = 10;
        type_option.comment = "Group options";
        type_option.strobe = 1'b1;
        type_option.merge_instances = 1'b0;
        cp_opt_val1: coverpoint opt_value_1 {
            option.goal = 95;
            option.auto_bin_max = 200;
            option.comment = "Value 1 options";
            option.detect_overlap = 1'b0;
            bins b1[] = {[0:100]};
        }
        cp_opt_val2: coverpoint opt_value_2 {
            option.weight = 5;
            bins b2 = {0, 1, 2, 3};
        }
        cross cp_opt_val1, cp_opt_val2;
    endgroup
    options_cg options_cg_inst;
    always_comb begin
        if (options_cg_inst == null) options_cg_inst = new();
        options_cg_inst.sample();
        opt_out = opt_value_1;
    end
endmodule
module covergroup_bins_types_module (
    input logic [3:0] bin_state_in,
    output logic [3:0] bin_state_out
);
    covergroup bins_types_cg @(bin_state_in);
        cp_bin_state: coverpoint bin_state_in {
            bins valid_bins[] = {0, 1, 2, 3};
            bins specific_bin = {5};
            illegal_bins error_bins = {8, 9};
            illegal_bins other_errors[] = {10, 11};
            ignore_bins ignore_values = {15};
        }
    endgroup
    bins_types_cg bins_types_cg_inst;
    always_comb begin
        if (bins_types_cg_inst == null) bins_types_cg_inst = new();
        bins_types_cg_inst.sample();
        bin_state_out = bin_state_in;
    end
endmodule
module covergroup_bins_features_module (
    input bit features_clk,
    input int features_data,
    input bit features_condition,
    output int features_out
);
    const int preset_vals_arr[] = {100, 101, 102};
    covergroup bins_features_cg (int data_param, bit condition_param) @(posedge features_clk);
        cp_features_data: coverpoint data_param iff (condition_param) {
            bins sized_bins[10] = {[0:99]};
            bins even_data[] = {[0:99]} with (item % 2 == 0);
            bins preset_bins[] = preset_vals_arr;
            bins calculated_bins[] = {(data_param + 1)};
            bins complex_bins[] = { [20:30], 40 } with (item != 25);
            bins default_bins = default;
        }
    endgroup
    bins_features_cg bins_features_cg_inst;
    always_ff @(posedge features_clk) begin
        if (bins_features_cg_inst == null) begin
            bins_features_cg_inst = new(features_data, features_condition);
        end
        bins_features_cg_inst.sample();
        features_out = features_data;
    end
endmodule
module covergroup_trans_bins_module (
    input bit trans_clk,
    input logic [2:0] trans_state,
    output logic [2:0] trans_out
);
    covergroup trans_bins_cg (logic [2:0] state_param) @(posedge trans_clk);
        cp_trans_state: coverpoint state_param {
            bins trans_0_to_1 = (3'd0 => 3'd1);
            bins trans_seq = (3'd0 => 3'd1, 3'd1 => 3'd2);
            bins trans_consec_3 = (3'd0 => 3'd1[*3]);
            bins trans_consec_range = (3'd0 => 3'd1[*1:5]);
            bins trans_nonconsec_3 = (3'd0 => 3'd1[=3]);
            bins trans_nonconsec_range = (3'd0 => 3'd1[=1:5]);
            bins trans_goto_3 = (3'd0 => 3'd1[->3]);
            bins trans_goto_range = (3'd0 => 3'd1[->1:5]);
            bins trans_sets = ({3'd0, 3'd1} => {3'd2, 3'd3});
            bins trans_list_items = (3'd0, 3'd1, 3'd2, 3'd3);
            bins trans_expr = (state_param => state_param + 3'd1);
        }
    endgroup
    trans_bins_cg trans_bins_cg_inst;
    always_ff @(posedge trans_clk) begin
        if (trans_bins_cg_inst == null) begin
            trans_bins_cg_inst = new(trans_state);
        end
        trans_bins_cg_inst.sample();
        trans_out = trans_state;
    end
endmodule
module covergroup_cross_basic_module (
    input bit cross_basic_clk,
    input logic [3:0] cross_basic_addr,
    input logic [7:0] cross_basic_data,
    input bit cross_basic_condition,
    output bit cross_basic_sync
);
    covergroup cross_basic_cg @(posedge cross_basic_clk);
        cp_cross_basic_addr: coverpoint cross_basic_addr iff (cross_basic_condition);
        cp_cross_basic_data: coverpoint cross_basic_data iff (cross_basic_condition);
        cross cp_cross_basic_addr, cp_cross_basic_data;
    endgroup
    cross_basic_cg cross_basic_cg_inst;
    always_ff @(posedge cross_basic_clk) begin
        if (cross_basic_cg_inst == null) cross_basic_cg_inst = new();
        cross_basic_cg_inst.sample();
        cross_basic_sync = 1'b1;
    end
endmodule
module covergroup_real_module (
    input bit real_clk,
    input real real_val_in,
    output real real_val_out
);
    // slang does not support real-valued coverpoints; replace with int for test diversity
    int real_val_int;
    always_ff @(posedge real_clk) real_val_int <= int'(real_val_in);
    covergroup real_cg @(posedge real_clk);
        coverpoint real_val_int;
        cp_real_explicit_nobins: coverpoint real_val_int;
        cp_real_explicit_withbins: coverpoint real_val_int {
            bins b_single = {1};
            bins b_range[] = { [0:10] };
            // removed illegal 'with', 'wildcard_real', transition bins, and default array bins
        }
    endgroup
    real_cg real_cg_inst;
    always_ff @(posedge real_clk) begin
        if (real_cg_inst == null) real_cg_inst = new();
        real_cg_inst.sample();
        real_val_out = real_val_in;
    end
endmodule
module covergroup_cross_binsof_module (
    input bit cross_select_clk,
    input logic [1:0] select_s1,
    input logic [1:0] select_s2,
    output logic [3:0] select_out
);
    covergroup cross_select_cg @(posedge cross_select_clk);
        cp_select_s1: coverpoint select_s1;
        cp_select_s2: coverpoint select_s2;
        cross cp_select_s1, cp_select_s2 {
            bins select_cond = binsof(cp_select_s1) intersect {0};
            // removed illegal/unparsable binsof/bin expressions for slang compatibility
        }
    endgroup
    cross_select_cg cross_select_cg_inst;
    always_ff @(posedge cross_select_clk) begin
        if (cross_select_cg_inst == null) cross_select_cg_inst = new();
        cross_select_cg_inst.sample();
        select_out = {select_s1, select_s2};
    end
endmodule
class base_cls_for_inherit;
    event dummy_event;
    covergroup base_cg @(dummy_event);
        cp_base: coverpoint 1 {
            bins base_b = {1};
        }
        type_option.goal = 50;
    endgroup : base_cg
    function void sample_base(bit trigger);
        if (trigger) -> dummy_event;
    endfunction
endclass
class derived_cls_for_inherit extends base_cls_for_inherit;
    event another_dummy_event;
    covergroup derived_cg /*extends base_cg*/ @(another_dummy_event); // slang does not support covergroup inheritance, flatten structure
        cp_derived: coverpoint 0 {
            bins derived_b = {0};
        }
        type_option.weight = 20;
        option.comment = "Derived options";
    endgroup : derived_cg
    function void sample_derived(bit trigger);
        if (trigger) -> another_dummy_event;
    endfunction
endclass
module class_covergroup_inherit_module (
    input bit inherit_trigger,
    output int inherit_dummy_out
);
    derived_cls_for_inherit derived_inst;
    initial begin
        derived_inst = new();
    end
    always_comb begin
        if (derived_inst != null && inherit_trigger) begin
            derived_inst.derived_cg.sample();
        end
        inherit_dummy_out = inherit_trigger ? 1 : 0;
    end
endmodule
