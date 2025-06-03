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
// \src: ../../top_ultra_minimal.sv:11.1-59.10
struct p_topi : public module {
	// \src: ../../top_ultra_minimal.sv:21.16-21.20
	// \unused_bits: 0 1 2 3 4 5 6 7
	wire<12> p___01__;
	// \src: ../../top_ultra_minimal.sv:34.15-34.19
	wire<7> p___11__;
	// \src: ../../top_ultra_minimal.sv:35.10-35.26
	value<1> p_celloutsig__1__19z;
	value<1> prev_p_celloutsig__1__19z;
	bool negedge_p_celloutsig__1__19z() const {
		return prev_p_celloutsig__1__19z.slice<0>().val() && !p_celloutsig__1__19z.slice<0>().val();
	}
	// \src: ../../top_ultra_minimal.sv:16.18-16.28
	/*input*/ value<96> p_clkin__data;
	value<96> prev_p_clkin__data;
	bool posedge_p_clkin__data_0() const {
		return !prev_p_clkin__data.slice<0>().val() && p_clkin__data.slice<0>().val();
	}
	// \src: ../../top_ultra_minimal.sv:17.19-17.26
	/*input*/ value<192> p_in__data;
	// \src: ../../top_ultra_minimal.sv:18.23-18.40
	/*output*/ value<8> p_inj__param__out__547;
	// \src: ../../top_ultra_minimal.sv:24.10-24.25
	/*outline*/ value<1> p_celloutsig__0__0z;
	// \src: ../../top_ultra_minimal.sv:25.10-25.25
	/*outline*/ value<1> p_celloutsig__0__2z;
	// \src: ../../top_ultra_minimal.sv:26.10-26.25
	/*outline*/ value<1> p_celloutsig__0__3z;
	// \src: ../../top_ultra_minimal.sv:27.16-27.31
	/*outline*/ value<8> p_celloutsig__0__8z;
	p_topi(interior) {}
	p_topi() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		if (p___01__.commit(observer)) changed = true;
		if (p___11__.commit(observer)) changed = true;
		prev_p_celloutsig__1__19z = p_celloutsig__1__19z;
		prev_p_clkin__data = p_clkin__data;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();
	debug_outline debug_eval_outline { std::bind(&p_topi::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_topi

void p_topi::reset() {
}

bool p_topi::eval(performer *performer) {
	bool converged = true;
	bool negedge_p_celloutsig__1__19z = this->negedge_p_celloutsig__1__19z();
	bool posedge_p_clkin__data_0 = this->posedge_p_clkin__data_0();
	// \src: ../../top_ultra_minimal.sv:26.10-26.25
	value<1> p_celloutsig__0__3z;
	// cells $reduce_or$../../top_ultra_minimal.sv:47$7 $logic_not$../../top_ultra_minimal.sv:46$6 $ternary$../../top_ultra_minimal.sv:46$5 $reduce_or$../../top_ultra_minimal.sv:45$4
	p_celloutsig__0__3z = reduce_or<1>(p___11__.curr.concat(logic_not<1>((reduce_or<1>(p_in__data.slice<84,76>().val()) ? value<1>{0x1u} : p_in__data.slice<47>().val()))).concat(p_in__data.slice<15,3>()).val());
	// \src: ../../top_ultra_minimal.sv:36.31-36.62
	// cell $eqx$../../top_ultra_minimal.sv:36$2
	p_celloutsig__1__19z = eqx_uu<1>(p___01__.curr.slice<11,8>().val(), p_in__data.slice<168,166>().val());
	// \always_ff: 1
	// \src: ../../top_ultra_minimal.sv:30.5-32.38
	// cell $procdff$14
	if (posedge_p_clkin__data_0) {
		p___01__.next = p_in__data.slice<107,96>().val();
	}
	if (p_clkin__data.slice<64>().val() == value<1> {1u}) {
		p___01__.next = value<12>{0u};
	}
	// \always_ff: 1
	// \src: ../../top_ultra_minimal.sv:38.5-40.37
	// cell $procdff$11
	if (negedge_p_celloutsig__1__19z) {
		p___11__.next = p_in__data.slice<48,42>().val();
	}
	if (p_clkin__data.slice<32>().val() == value<1> {1u}) {
		p___11__.next = value<7>{0u};
	}
	// \src: ../../top_ultra_minimal.sv:50.30-50.130
	// cell $xnor$../../top_ultra_minimal.sv:50$8
	p_inj__param__out__547 = xnor_uu<8>(p___11__.curr, p___11__.curr.slice<5,0>().concat(p_celloutsig__0__3z.repeat<2>()).val());
	return converged;
}

void p_topi::debug_eval() {
	// \src: ../../top_ultra_minimal.sv:45.30-45.46
	// cell $reduce_or$../../top_ultra_minimal.sv:45$4
	p_celloutsig__0__0z = reduce_or<1>(p_in__data.slice<84,76>().val());
	// cells $logic_not$../../top_ultra_minimal.sv:46$6 $ternary$../../top_ultra_minimal.sv:46$5 $reduce_or$../../top_ultra_minimal.sv:45$4
	p_celloutsig__0__2z = logic_not<1>((p_celloutsig__0__0z ? value<1>{0x1u} : p_in__data.slice<47>().val()));
	// cells $reduce_or$../../top_ultra_minimal.sv:47$7 $logic_not$../../top_ultra_minimal.sv:46$6 $ternary$../../top_ultra_minimal.sv:46$5 $reduce_or$../../top_ultra_minimal.sv:45$4
	p_celloutsig__0__3z = reduce_or<1>(p___11__.curr.concat(p_celloutsig__0__2z).concat(p_in__data.slice<15,3>()).val());
	// \src: ../../top_ultra_minimal.sv:50.30-50.130
	// cell $xnor$../../top_ultra_minimal.sv:50$8
	p_celloutsig__0__8z = xnor_uu<8>(p___11__.curr, p___11__.curr.slice<5,0>().concat(p_celloutsig__0__3z.repeat<2>()).val());
}

CXXRTL_EXTREMELY_COLD
void p_topi::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "topi", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../../top_ultra_minimal.sv:11.1-59.10" },
		}), std::move(cell_attrs));
		scopes->add(path, "module_with_params_inst_1000", "module_with_params", "src\000s../../top_ultra_minimal.sv:2.1-9.10\000", "src\000s../../top_ultra_minimal.sv:53.24-56.6\000");
	}
	if (items) {
		items->add(path, "module_with_params_inst_1000 param_out", "src\000s../../top_ultra_minimal.sv:6.23-6.32\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "module_with_params_inst_1000 param_in", "src\000s../../top_ultra_minimal.sv:5.22-5.30\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "_01_", "src\000s../../top_ultra_minimal.sv:21.16-21.20\000unused_bits\000s0 1 2 3 4 5 6 7\000", p___01__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "_11_", "src\000s../../top_ultra_minimal.sv:34.15-34.19\000", p___11__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "celloutsig_0_0z", "src\000s../../top_ultra_minimal.sv:24.10-24.25\000", debug_eval_outline, p_celloutsig__0__0z);
		items->add(path, "celloutsig_0_2z", "src\000s../../top_ultra_minimal.sv:25.10-25.25\000", debug_eval_outline, p_celloutsig__0__2z);
		items->add(path, "celloutsig_0_3z", "src\000s../../top_ultra_minimal.sv:26.10-26.25\000", debug_eval_outline, p_celloutsig__0__3z);
		items->add(path, "celloutsig_0_8z", "src\000s../../top_ultra_minimal.sv:27.16-27.31\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "celloutsig_1_19z", "src\000s../../top_ultra_minimal.sv:35.10-35.26\000", p_celloutsig__1__19z, 0, debug_item::DRIVEN_COMB);
		items->add(path, "clkin_data", "src\000s../../top_ultra_minimal.sv:16.18-16.28\000", p_clkin__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "in_data", "src\000s../../top_ultra_minimal.sv:17.19-17.26\000", p_in__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_param_out_547", "src\000s../../top_ultra_minimal.sv:18.23-18.40\000", p_inj__param__out__547, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_topi>(new cxxrtl_design::p_topi) };
}
