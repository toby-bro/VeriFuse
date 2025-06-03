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
// \src: ../../top_minimal.sv:11.1-41.10
struct p_topi : public module {
	// \src: ../../top_minimal.sv:15.19-15.26
	/*input*/ value<192> p_in__data;
	// \src: ../../top_minimal.sv:16.23-16.40
	/*output*/ value<8> p_inj__param__out__547;
	// \src: ../../top_minimal.sv:19.10-19.25
	/*outline*/ value<1> p_celloutsig__0__0z;
	// \src: ../../top_minimal.sv:20.10-20.25
	/*outline*/ value<1> p_celloutsig__0__2z;
	// \src: ../../top_minimal.sv:21.10-21.25
	/*outline*/ value<1> p_celloutsig__0__3z;
	// \src: ../../top_minimal.sv:22.16-22.31
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
	// \src: ../../top_minimal.sv:21.10-21.25
	value<1> p_celloutsig__0__3z;
	// cells $reduce_or$../../top_minimal.sv:31$4 $logic_not$../../top_minimal.sv:28$3 $ternary$../../top_minimal.sv:28$2 $reduce_or$../../top_minimal.sv:27$1
	p_celloutsig__0__3z = reduce_or<1>(logic_not<1>((reduce_or<1>(p_in__data.slice<84,76>().val()) ? value<1>{0x1u} : p_in__data.slice<47>().val())).concat(p_in__data.slice<48,41>()).concat(p_in__data.slice<15,3>()).val());
	// \src: ../../top_minimal.sv:34.30-34.130
	// cell $xnor$../../top_minimal.sv:34$5
	p_inj__param__out__547 = xnor_uu<8>(p_in__data.slice<48,44>().concat(p_in__data.slice<41>()).concat(p_in__data.slice<42>()).val(), p_in__data.slice<47,44>().concat(p_in__data.slice<41>()).concat(p_in__data.slice<42>()).concat(p_celloutsig__0__3z.repeat<2>()).val());
	return converged;
}

void p_topi::debug_eval() {
	// \src: ../../top_minimal.sv:27.30-27.46
	// cell $reduce_or$../../top_minimal.sv:27$1
	p_celloutsig__0__0z = reduce_or<1>(p_in__data.slice<84,76>().val());
	// cells $logic_not$../../top_minimal.sv:28$3 $ternary$../../top_minimal.sv:28$2 $reduce_or$../../top_minimal.sv:27$1
	p_celloutsig__0__2z = logic_not<1>((p_celloutsig__0__0z ? value<1>{0x1u} : p_in__data.slice<47>().val()));
	// cells $reduce_or$../../top_minimal.sv:31$4 $logic_not$../../top_minimal.sv:28$3 $ternary$../../top_minimal.sv:28$2 $reduce_or$../../top_minimal.sv:27$1
	p_celloutsig__0__3z = reduce_or<1>(p_celloutsig__0__2z.concat(p_in__data.slice<48,41>()).concat(p_in__data.slice<15,3>()).val());
	// \src: ../../top_minimal.sv:34.30-34.130
	// cell $xnor$../../top_minimal.sv:34$5
	p_celloutsig__0__8z = xnor_uu<8>(p_in__data.slice<48,44>().concat(p_in__data.slice<41>()).concat(p_in__data.slice<42>()).val(), p_in__data.slice<47,44>().concat(p_in__data.slice<41>()).concat(p_in__data.slice<42>()).concat(p_celloutsig__0__3z.repeat<2>()).val());
}

CXXRTL_EXTREMELY_COLD
void p_topi::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "topi", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../../top_minimal.sv:11.1-41.10" },
		}), std::move(cell_attrs));
		scopes->add(path, "module_with_params_inst_1000", "module_with_params", "src\000s../../top_minimal.sv:2.1-9.10\000", "src\000s../../top_minimal.sv:37.24-40.6\000");
	}
	if (items) {
		items->add(path, "module_with_params_inst_1000 param_out", "src\000s../../top_minimal.sv:6.23-6.32\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "module_with_params_inst_1000 param_in", "src\000s../../top_minimal.sv:5.22-5.30\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "celloutsig_0_0z", "src\000s../../top_minimal.sv:19.10-19.25\000", debug_eval_outline, p_celloutsig__0__0z);
		items->add(path, "celloutsig_0_2z", "src\000s../../top_minimal.sv:20.10-20.25\000", debug_eval_outline, p_celloutsig__0__2z);
		items->add(path, "celloutsig_0_3z", "src\000s../../top_minimal.sv:21.10-21.25\000", debug_eval_outline, p_celloutsig__0__3z);
		items->add(path, "celloutsig_0_8z", "src\000s../../top_minimal.sv:22.16-22.31\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "in_data", "src\000s../../top_minimal.sv:15.19-15.26\000", p_in__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_param_out_547", "src\000s../../top_minimal.sv:16.23-16.40\000", p_inj__param__out__547, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_topi>(new cxxrtl_design::p_topi) };
}
