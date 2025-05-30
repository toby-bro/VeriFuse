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
// \src: ../expr_postsub_comb.sv:1.1-13.10
struct p_expr__postsub__comb : public module {
	// \src: ../expr_postsub_comb.sv:2.23-2.32
	/*input*/ value<8> p_in__val__m2;
	// \src: ../expr_postsub_comb.sv:4.24-4.35
	/*output*/ value<8> p_out__diff__m2;
	// \src: ../expr_postsub_comb.sv:3.23-3.33
	/*input*/ value<8> p_sub__val__m2;
	// \src: ../expr_postsub_comb.sv:5.24-5.34
	/*output*/ value<8> p_var__out__m2;
	p_expr__postsub__comb(interior) {}
	p_expr__postsub__comb() {
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

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_expr__postsub__comb

void p_expr__postsub__comb::reset() {
}

bool p_expr__postsub__comb::eval(performer *performer) {
	bool converged = true;
	// \src: ../expr_postsub_comb.sv:0.0-0.0
	// cell $sub$../expr_postsub_comb.sv:0$2
	p_var__out__m2 = sub_uu<8>(p_in__val__m2, value<1>{0x1u});
	// cells $sub$../expr_postsub_comb.sv:10$4 $sub$../expr_postsub_comb.sv:10$3
	p_out__diff__m2 = sub_uu<8>(sub_uu<8>(p_var__out__m2, value<1>{0x1u}), p_sub__val__m2);
	return converged;
}

void p_expr__postsub__comb::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_expr__postsub__comb::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "expr_postsub_comb", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../expr_postsub_comb.sv:1.1-13.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "in_val_m2", "src\000s../expr_postsub_comb.sv:2.23-2.32\000", p_in__val__m2, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "out_diff_m2", "src\000s../expr_postsub_comb.sv:4.24-4.35\000", p_out__diff__m2, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "sub_val_m2", "src\000s../expr_postsub_comb.sv:3.23-3.33\000", p_sub__val__m2, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "var_m2", "src\000s../expr_postsub_comb.sv:7.17-7.23\000", debug_alias(), p_var__out__m2);
		items->add(path, "var_out_m2", "src\000s../expr_postsub_comb.sv:5.24-5.34\000", p_var__out__m2, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_expr__postsub__comb>(new cxxrtl_design::p_expr__postsub__comb) };
}
