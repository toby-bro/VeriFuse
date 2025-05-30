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
// \src: ../topi.sv:1.8
struct p_expr__postsub__comb : public module {
	// \src: ../topi.sv:5.24
	/*output*/ value<8> p_var__out__m2;
	// \src: ../topi.sv:4.24
	/*output*/ value<8> p_out__diff__m2;
	// \src: ../topi.sv:3.23
	/*input*/ value<8> p_sub__val__m2;
	// \src: ../topi.sv:2.23
	/*input*/ value<8> p_in__val__m2;
	// \src: ../topi.sv:7.17
	/*outline*/ value<8> p_var__m2;
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
	debug_outline debug_eval_outline { std::bind(&p_expr__postsub__comb::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_expr__postsub__comb

void p_expr__postsub__comb::reset() {
}

bool p_expr__postsub__comb::eval(performer *performer) {
	bool converged = true;
	value<8> i_auto_24_builder_2e_cc_3a_338_3a_Biop_24_3;
	// cell $auto$builder.cc:330:Biop$2
	i_auto_24_builder_2e_cc_3a_338_3a_Biop_24_3 = sub_uu<8>(p_in__val__m2, value<2>{0x1u});
	// connection
	p_var__out__m2 = i_auto_24_builder_2e_cc_3a_338_3a_Biop_24_3;
	// cell $auto$builder.cc:330:Biop$4
	p_out__diff__m2 = sub_uu<8>(i_auto_24_builder_2e_cc_3a_338_3a_Biop_24_3, p_sub__val__m2);
	return converged;
}

void p_expr__postsub__comb::debug_eval() {
	// connection
	p_var__m2 = sub_uu<8>(p_in__val__m2, value<2>{0x1u});
}

CXXRTL_EXTREMELY_COLD
void p_expr__postsub__comb::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "expr_postsub_comb", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../topi.sv:1.8" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "var_m2", "src\000s../topi.sv:7.17\000", debug_eval_outline, p_var__m2);
		items->add(path, "var_out_m2", "src\000s../topi.sv:5.24\000", p_var__out__m2, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "out_diff_m2", "src\000s../topi.sv:4.24\000", p_out__diff__m2, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "sub_val_m2", "src\000s../topi.sv:3.23\000", p_sub__val__m2, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "in_val_m2", "src\000s../topi.sv:2.23\000", p_in__val__m2, 0, debug_item::INPUT|debug_item::UNDRIVEN);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_expr__postsub__comb>(new cxxrtl_design::p_expr__postsub__comb) };
}
