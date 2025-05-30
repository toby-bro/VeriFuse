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
// \src: ../stmt_if_task.sv:1.1-19.10
struct p_stmt__if__task : public module {
	// \src: ../stmt_if_task.sv:4.15-4.27
	/*input*/ value<1> p_condition__m6;
	// \src: ../stmt_if_task.sv:3.23-3.32
	/*input*/ value<8> p_in__val__m6;
	// \src: ../stmt_if_task.sv:2.24-2.34
	/*output*/ value<8> p_out__val__m6;
	// \src: ../stmt_if_task.sv:6.17-6.23
	/*outline*/ value<8> p_var__m6;
	p_stmt__if__task(interior) {}
	p_stmt__if__task() {
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
	debug_outline debug_eval_outline { std::bind(&p_stmt__if__task::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_stmt__if__task

void p_stmt__if__task::reset() {
}

bool p_stmt__if__task::eval(performer *performer) {
	bool converged = true;
	// \src: ../stmt_if_task.sv:0.0-0.0
	// cell $sub$../stmt_if_task.sv:0$2
	p_out__val__m6 = sub_uu<32>(p_in__val__m6, value<32>{0x1u}).slice<7,0>().val();
	return converged;
}

void p_stmt__if__task::debug_eval() {
	// \src: ../stmt_if_task.sv:0.0-0.0
	// cell $sub$../stmt_if_task.sv:0$2
	p_var__m6 = sub_uu<32>(p_in__val__m6, value<32>{0x1u}).slice<7,0>().val();
}

CXXRTL_EXTREMELY_COLD
void p_stmt__if__task::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "stmt_if_task", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../stmt_if_task.sv:1.1-19.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "var_m6", "src\000s../stmt_if_task.sv:6.17-6.23\000", debug_eval_outline, p_var__m6);
		items->add(path, "condition_m6", "src\000s../stmt_if_task.sv:4.15-4.27\000", p_condition__m6, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "in_val_m6", "src\000s../stmt_if_task.sv:3.23-3.32\000", p_in__val__m6, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "out_val_m6", "src\000s../stmt_if_task.sv:2.24-2.34\000", p_out__val__m6, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_stmt__if__task>(new cxxrtl_design::p_stmt__if__task) };
}
