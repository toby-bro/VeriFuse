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

// \keep: 1
// \top: 1
// \src: bug.sv:1.1-13.10
struct p_bug : public module {
	// \src: bug.sv:2.15-2.22
	wire<7> p_reg__bug;
	// \src: bug.sv:3.9-3.12
	/*outline*/ value<1> p_clk;
	value<1> cell_i_display_24_bug_2e_sv_3a_10_24_4;
	p_bug(interior) {}
	p_bug() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		if (p_reg__bug.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();
	debug_outline debug_eval_outline { std::bind(&p_bug::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_bug

void p_bug::reset() {
	cell_i_display_24_bug_2e_sv_3a_10_24_4 = {};
}

bool p_bug::eval(performer *performer) {
	bool converged = true;
	// cells $display$bug.sv:10$4 $ternary$bug.sv:11$6 $eq$bug.sv:11$5
	if (!cell_i_display_24_bug_2e_sv_3a_10_24_4) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "reg_bug=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " expected=0011111 ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::STRING, "", fmt_part::RIGHT, (char)32, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<32> arg1;
				value<7> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = (eq_uu<1>(p_reg__bug.curr, value<7>{0x1fu}) ? value<32>{0x50415353u} : value<32>{0x4641494cu});
			formatter.arg0 = p_reg__bug.curr;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "bug.sv:10.12-11.70" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24_bug_2e_sv_3a_10_24_4 = value<1>{1u};
	}
	// \always_ff: 1
	// \src: bug.sv:5.5-6.31
	// cell $procdff$7
	return converged;
}

void p_bug::debug_eval() {
	// connection
	p_clk = value<1>{0x1u};
	// connection
	p_clk = value<1>{0u};
}

CXXRTL_EXTREMELY_COLD
void p_bug::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "bug", metadata_map({
			{ "keep", UINT64_C(1) },
			{ "top", UINT64_C(1) },
			{ "src", "bug.sv:1.1-13.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "clk", "src\000sbug.sv:3.9-3.12\000", debug_eval_outline, p_clk);
		items->add(path, "reg_bug", "src\000sbug.sv:2.15-2.22\000", p_reg__bug, 0, debug_item::DRIVEN_SYNC);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_bug>(new cxxrtl_design::p_bug) };
}
