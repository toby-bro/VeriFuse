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
// \src: <<EOT:1.1-8.10
struct p_top : public module {
	// \src: <<EOT:2.14-2.17
	/*input*/ value<1> p_clk;
	value<1> prev_p_clk;
	bool negedge_p_clk() const {
		return prev_p_clk.slice<0>().val() && !p_clk.slice<0>().val();
	}
	// \src: <<EOT:3.21-3.28
	/*output*/ wire<7> p_reg__bug;
	p_top(interior) {}
	p_top() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		prev_p_clk = p_clk;
		if (p_reg__bug.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_top

void p_top::reset() {
}

bool p_top::eval(performer *performer) {
	bool converged = true;
	bool negedge_p_clk = this->negedge_p_clk();
	// \always_ff: 1
	// \src: <<EOT:6.2-7.25
	// cell $procdff$2
	if (negedge_p_clk) {
		p_reg__bug.next = value<7>{0x1fu};
	}
	return converged;
}

void p_top::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_top::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "top", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "<<EOT:1.1-8.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "clk", "src\000s<<EOT:2.14-2.17\000", p_clk, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "reg_bug", "src\000s<<EOT:3.21-3.28\000", p_reg__bug, 0, debug_item::OUTPUT|debug_item::DRIVEN_SYNC);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_top>(new cxxrtl_design::p_top) };
}
