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
// \src: ../../countbits_ops.sv:1.1-6.10
struct p_countbits__ops : public module {
	// \src: ../../countbits_ops.sv:3.24-3.27
	/*output*/ value<4> p_cnt;
	// \src: ../../countbits_ops.sv:2.23-2.27
	/*input*/ value<8> p_in__d;
	p_countbits__ops(interior) {}
	p_countbits__ops() {
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
}; // struct p_countbits__ops

void p_countbits__ops::reset() {
}

bool p_countbits__ops::eval(performer *performer) {
	bool converged = true;
	// cells $add$../../countbits_ops.sv:5$64 $logic_or$../../countbits_ops.sv:0$63 $eqx$../../countbits_ops.sv:0$62 $eqx$../../countbits_ops.sv:0$59 $add$../../countbits_ops.sv:0$56 $logic_or$../../countbits_ops.sv:0$55 $eqx$../../countbits_ops.sv:0$54 $eqx$../../countbits_ops.sv:0$51 $add$../../countbits_ops.sv:0$48 $logic_or$../../countbits_ops.sv:0$47 $eqx$../../countbits_ops.sv:0$46 $eqx$../../countbits_ops.sv:0$43 $add$../../countbits_ops.sv:0$40 $logic_or$../../countbits_ops.sv:0$39 $eqx$../../countbits_ops.sv:0$38 $eqx$../../countbits_ops.sv:0$35 $add$../../countbits_ops.sv:0$32 $logic_or$../../countbits_ops.sv:0$31 $eqx$../../countbits_ops.sv:0$30 $eqx$../../countbits_ops.sv:0$27 $add$../../countbits_ops.sv:0$24 $logic_or$../../countbits_ops.sv:0$23 $eqx$../../countbits_ops.sv:0$22 $eqx$../../countbits_ops.sv:0$19 $add$../../countbits_ops.sv:0$16 $logic_or$../../countbits_ops.sv:0$15 $eqx$../../countbits_ops.sv:0$14 $eqx$../../countbits_ops.sv:0$11 $add$../../countbits_ops.sv:0$8 $logic_or$../../countbits_ops.sv:0$7 $eqx$../../countbits_ops.sv:0$6 $eqx$../../countbits_ops.sv:0$3
	p_cnt = add_uu<32>(add_uu<32>(add_uu<32>(add_uu<32>(add_uu<32>(add_uu<32>(add_uu<32>(add_uu<32>(value<32>{0u}, logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<7>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<7>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<6>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<6>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<5>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<5>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<4>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<4>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<3>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<3>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<2>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<2>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<1>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<1>()).val(), value<1>{0u}))), logic_or<32>(eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<0>()).val(), value<1>{0x1u}), eqx_uu<1>(value<7>{0u}.concat(p_in__d.slice<0>()).val(), value<1>{0u}))).slice<3,0>().val();
	return converged;
}

void p_countbits__ops::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_countbits__ops::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "countbits_ops", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../../countbits_ops.sv:1.1-6.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "cnt", "src\000s../../countbits_ops.sv:3.24-3.27\000", p_cnt, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "in_d", "src\000s../../countbits_ops.sv:2.23-2.27\000", p_in__d, 0, debug_item::INPUT|debug_item::UNDRIVEN);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_countbits__ops>(new cxxrtl_design::p_countbits__ops) };
}
