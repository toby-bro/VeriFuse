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
// \src: ultra_minimal.sv:2.1-22.10
struct p_bug : public module {
	// \src: ultra_minimal.sv:7.15-7.22
	wire<7> p_reg__bug;
	value<1> cell_i_display_24_ultra__minimal_2e_sv_3a_19_24_4;
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

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_bug

void p_bug::reset() {
	cell_i_display_24_ultra__minimal_2e_sv_3a_19_24_4 = {};
}

bool p_bug::eval(performer *performer) {
	bool converged = true;
	// \src: ultra_minimal.sv:20.29-20.66
	value<24> i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_10;
	// cells $ternary$ultra_minimal.sv:20$6 $eq$ultra_minimal.sv:20$5
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_10.slice<2,0>() = (eq_uu<1>(p_reg__bug.curr, value<5>{0x1fu}) ? value<3>{0x3u} : value<3>{0x7u});
	// connection
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_10.slice<23,3>() = value<21>{0x1c5392u};
	// \always_ff: 1
	// \src: ultra_minimal.sv:11.5-15.38
	// cell $procdff$9
	if (value<1>{0u} == value<1> {1u}) {
		p_reg__bug.next = value<7>{0u};
	}
	// \src: ultra_minimal.sv:19.12-20.68
	// cell $display$ultra_minimal.sv:19$4
	if (!cell_i_display_24_ultra__minimal_2e_sv_3a_19_24_4) {
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
				value<24> arg1;
				value<7> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = value<21>{0x1c5392u}.concat(i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_10.slice<2,0>()).val();
			formatter.arg0 = p_reg__bug.curr;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "ultra_minimal.sv:19.12-20.68" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24_ultra__minimal_2e_sv_3a_19_24_4 = value<1>{1u};
	}
	return converged;
}

void p_bug::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_bug::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "bug", metadata_map({
			{ "keep", UINT64_C(1) },
			{ "top", UINT64_C(1) },
			{ "src", "ultra_minimal.sv:2.1-22.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		static const value<1> const_p_clk = value<1>{0u};
		items->add(path, "clk", "src\000sultra_minimal.sv:8.9-8.12\000", const_p_clk);
		static const value<7> const_p_expected__data = value<7>{0x1fu};
		items->add(path, "expected_data", "src\000sultra_minimal.sv:5.16-5.29\000", const_p_expected__data);
		items->add(path, "reg_bug", "src\000sultra_minimal.sv:7.15-7.22\000", p_reg__bug, 0, debug_item::DRIVEN_SYNC);
		static const value<1> const_p_reset = value<1>{0u};
		items->add(path, "reset", "src\000sultra_minimal.sv:4.10-4.15\000", const_p_reset);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_bug>(new cxxrtl_design::p_bug) };
}
