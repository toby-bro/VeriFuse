#include <cxxrtl/cxxrtl.h>

#if defined(CXXRTL_INCLUDE_CAPI_IMPL) || \
    defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi.cc>
#endif

#if defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi_vcd.cc>
#endif

using namespace cxxrtl_yosys;

namespace cxxrtl_design {

// \top: 1
// \interfaces_replaced_in_module: 1
// \src: ../../countbits_ops.sv:14.1-65.10
struct p_countbits__ops : public module {
	// \src: ../../countbits_ops.sv:15.16-15.19
	/*input*/ value<1> p_clk;
	value<1> prev_p_clk;
	bool posedge_p_clk() const {
		return !prev_p_clk.slice<0>().val() && p_clk.slice<0>().val();
	}
	// \src: ../../countbits_ops.sv:23.24-23.27
	/*output*/ value<4> p_cnt;
	// \src: ../../countbits_ops.sv:31.17-31.39
	// \unused_bits: 1 2 3 4 5 6 7
	wire<8> p_data__q__ts1755304956849;
	// \src: ../../countbits_ops.sv:16.23-16.27
	/*input*/ value<8> p_in__d;
	// \src: ../../countbits_ops.sv:24.18-24.54
	/*output*/ value<1> p_inj__control__status__1755304956867__645;
	// \src: ../../countbits_ops.sv:17.17-17.44
	/*input*/ value<1> p_inj__data0__1755304956858__225;
	// \src: ../../countbits_ops.sv:18.17-18.44
	/*input*/ value<1> p_inj__data1__1755304956858__180;
	// \src: ../../countbits_ops.sv:19.24-19.53
	/*input*/ value<16> p_inj__data__in__1755304956867__809;
	// \src: ../../countbits_ops.sv:20.15-20.42
	/*input*/ value<32> p_inj__in__val__1755304956862__68;
	// \src: ../../countbits_ops.sv:25.18-25.50
	/*output*/ value<1> p_inj__out__data__q__1755304956848__467;
	// \src: ../../countbits_ops.sv:26.16-26.45
	/*output*/ value<32> p_inj__out__val__1755304956862__657;
	// \src: ../../countbits_ops.sv:27.18-27.46
	/*output*/ value<1> p_inj__result__1755304956858__997;
	// \src: ../../countbits_ops.sv:21.17-21.42
	/*input*/ value<1> p_inj__sel__1755304956858__762;
	// \src: ../../countbits_ops.sv:22.16-22.19
	/*input*/ value<1> p_rst;
	wire<1> p_vif__inst_2e_data;
	// \src: ../../countbits_ops.sv:0.0-0.0
	/*outline*/ value<16> p_cif__inst_2e_control__reg;
	p_countbits__ops(interior) {}
	p_countbits__ops() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		prev_p_clk = p_clk;
		if (p_data__q__ts1755304956849.commit(observer)) changed = true;
		if (p_vif__inst_2e_data.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();
	debug_outline debug_eval_outline { std::bind(&p_countbits__ops::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_countbits__ops

void p_countbits__ops::reset() {
}

bool p_countbits__ops::eval(performer *performer) {
	bool converged = true;
	bool posedge_p_clk = this->posedge_p_clk();
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_153;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_154;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_155;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_103__Y;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_111__Y;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_119__Y;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_127__Y;
	// \src: ../../countbits_ops.sv:0.0-0.0
	value<32> i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_79__Y;
	// cells $logic_or$../../countbits_ops.sv:0$79 $eqx$../../countbits_ops.sv:0$75 $eqx$../../countbits_ops.sv:0$78
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_79__Y.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<7>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<7>().val(), value<1>{0u}));
	// connection
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_79__Y.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$87 $eqx$../../countbits_ops.sv:0$83 $eqx$../../countbits_ops.sv:0$86
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_154.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<6>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<6>().val(), value<1>{0u}));
	// connection
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_154.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$95 $eqx$../../countbits_ops.sv:0$91 $eqx$../../countbits_ops.sv:0$94
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_155.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<5>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<5>().val(), value<1>{0u}));
	// connection
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_155.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$103 $eqx$../../countbits_ops.sv:0$99 $eqx$../../countbits_ops.sv:0$102
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_103__Y.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<4>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<4>().val(), value<1>{0u}));
	// connection
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_103__Y.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$111 $eqx$../../countbits_ops.sv:0$107 $eqx$../../countbits_ops.sv:0$110
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_111__Y.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<3>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<3>().val(), value<1>{0u}));
	// connection
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_111__Y.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$119 $eqx$../../countbits_ops.sv:0$115 $eqx$../../countbits_ops.sv:0$118
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_119__Y.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<2>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<2>().val(), value<1>{0u}));
	// connection
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_119__Y.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$127 $eqx$../../countbits_ops.sv:0$123 $eqx$../../countbits_ops.sv:0$126
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_127__Y.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<1>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<1>().val(), value<1>{0u}));
	// connection
	i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_127__Y.slice<31,1>() = value<31>{0u};
	// cells $logic_or$../../countbits_ops.sv:0$135 $eqx$../../countbits_ops.sv:0$131 $eqx$../../countbits_ops.sv:0$134
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_153.slice<0>() = logic_or<1>(eqx_uu<1>(p_in__d.slice<0>().val(), value<1>{0x1u}), eqx_uu<1>(p_in__d.slice<0>().val(), value<1>{0u}));
	// connection
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_153.slice<31,1>() = value<31>{0u};
	// \src: ../../countbits_ops.sv:49.47-49.132
	// cell $ternary$../../countbits_ops.sv:49$71
	p_inj__result__1755304956858__997 = (p_inj__sel__1755304956858__762 ? p_inj__data1__1755304956858__180 : p_inj__data0__1755304956858__225);
	// \always_ff: 1
	// \src: ../../countbits_ops.sv:52.5-60.8
	// cell $procdff$145
	if (posedge_p_clk) {
		p_vif__inst_2e_data.next = p_in__d.slice<0>().val();
	}
	if (p_rst == value<1> {1u}) {
		p_vif__inst_2e_data.next = value<1>{0u};
	}
	// \always_ff: 1
	// \src: ../../countbits_ops.sv:52.5-60.8
	// cell $procdff$142
	if (posedge_p_clk) {
		p_data__q__ts1755304956849.next.slice<0>() = p_vif__inst_2e_data.curr;
	}
	if (p_rst == value<1> {1u}) {
		p_data__q__ts1755304956849.next.slice<0>() = value<1>{0u};
	}
	// cells $ne$../../countbits_ops.sv:40$70 $procmux$138
	p_inj__control__status__1755304956867__645 = reduce_bool<1>((p_inj__data0__1755304956858__225 ? p_inj__data__in__1755304956867__809 : value<16>{0u}));
	// cells $add$../../countbits_ops.sv:64$136 $add$../../countbits_ops.sv:0$128 $add$../../countbits_ops.sv:0$120 $add$../../countbits_ops.sv:0$112 $add$../../countbits_ops.sv:0$104 $add$../../countbits_ops.sv:0$96 $add$../../countbits_ops.sv:0$88 $add$../../countbits_ops.sv:0$80
	p_cnt = add_uu<4>(add_uu<4>(add_uu<4>(add_uu<4>(add_uu<4>(add_uu<4>(add_uu<3>(add_uu<2>(value<1>{0u}, i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_79__Y.slice<0>().val()), i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_154.slice<0>().val()), i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_155.slice<0>().val()), i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_103__Y.slice<0>().val()), i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_111__Y.slice<0>().val()), i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_119__Y.slice<0>().val()), i_logic__or_24__2e__2e__2f__2e__2e__2f_countbits__ops_2e_sv_3a_0_24_127__Y.slice<0>().val()), i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_153.slice<0>().val());
	// connection
	p_inj__out__val__1755304956862__657 = p_inj__in__val__1755304956862__68;
	// connection
	p_inj__out__data__q__1755304956848__467 = p_data__q__ts1755304956849.curr.slice<0>().val();
	return converged;
}

void p_countbits__ops::debug_eval() {
	// \full_case: 1
	// \src: ../../countbits_ops.sv:35.17-35.44|../../countbits_ops.sv:35.13-39.16
	// cell $procmux$138
	p_cif__inst_2e_control__reg = (p_inj__data0__1755304956858__225 ? p_inj__data__in__1755304956867__809 : value<16>{0u});
}

CXXRTL_EXTREMELY_COLD
void p_countbits__ops::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "countbits_ops", metadata_map({
			{ "top", UINT64_C(1) },
			{ "interfaces_replaced_in_module", UINT64_C(1) },
			{ "src", "../../countbits_ops.sv:14.1-65.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "cif_inst.control_reg", "src\000s../../countbits_ops.sv:0.0-0.0\000", debug_eval_outline, p_cif__inst_2e_control__reg);
		items->add(path, "clk", "src\000s../../countbits_ops.sv:15.16-15.19\000", p_clk, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "cnt", "src\000s../../countbits_ops.sv:23.24-23.27\000", p_cnt, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "data_q_ts1755304956849", "src\000s../../countbits_ops.sv:31.17-31.39\000unused_bits\000s1 2 3 4 5 6 7\000", p_data__q__ts1755304956849, 0, debug_item::UNDRIVEN|debug_item::DRIVEN_SYNC);
		items->add(path, "in_d", "src\000s../../countbits_ops.sv:16.23-16.27\000", p_in__d, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_control_status_1755304956867_645", "src\000s../../countbits_ops.sv:24.18-24.54\000", p_inj__control__status__1755304956867__645, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_data0_1755304956858_225", "src\000s../../countbits_ops.sv:17.17-17.44\000", p_inj__data0__1755304956858__225, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data1_1755304956858_180", "src\000s../../countbits_ops.sv:18.17-18.44\000", p_inj__data1__1755304956858__180, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_in_1755304956867_809", "src\000s../../countbits_ops.sv:19.24-19.53\000", p_inj__data__in__1755304956867__809, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_val_1755304956862_68", "src\000s../../countbits_ops.sv:20.15-20.42\000", p_inj__in__val__1755304956862__68, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out_data_q_1755304956848_467", "src\000s../../countbits_ops.sv:25.18-25.50\000", p_inj__out__data__q__1755304956848__467, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out_val_1755304956862_657", "src\000s../../countbits_ops.sv:26.16-26.45\000", p_inj__out__val__1755304956862__657, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_result_1755304956858_997", "src\000s../../countbits_ops.sv:27.18-27.46\000", p_inj__result__1755304956858__997, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_sel_1755304956858_762", "src\000s../../countbits_ops.sv:21.17-21.42\000", p_inj__sel__1755304956858__762, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "rst", "src\000s../../countbits_ops.sv:22.16-22.19\000", p_rst, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "vif_inst.data", "", p_vif__inst_2e_data, 0, debug_item::DRIVEN_SYNC);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_countbits__ops>(new cxxrtl_design::p_countbits__ops) };
}
