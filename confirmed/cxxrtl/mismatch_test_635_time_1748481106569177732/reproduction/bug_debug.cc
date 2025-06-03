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
// \keep: 1
// \src: <<EOT:1.1-14.10
struct p_bug__debug : public module {
	// \src: <<EOT:2.15-2.22
	wire<7> p_reg__bug;
	value<1> cell_i_display_24__3c__3c_EOT_3a_11_24_5;
	value<1> cell_i_display_24__3c__3c_EOT_3a_12_24_6;
	value<1> cell_i_display_24__3c__3c_EOT_3a_9_24_4;
	p_bug__debug(interior) {}
	p_bug__debug() {
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
}; // struct p_bug__debug

void p_bug__debug::reset() {
	cell_i_display_24__3c__3c_EOT_3a_11_24_5 = {};
	cell_i_display_24__3c__3c_EOT_3a_12_24_6 = {};
	cell_i_display_24__3c__3c_EOT_3a_9_24_4 = {};
}

bool p_bug__debug::eval(performer *performer) {
	bool converged = true;
	// \always_ff: 1
	// \src: <<EOT:5.5-6.31
	// cell $procdff$7
	// \src: <<EOT:9.9-9.61
	// cell $display$<<EOT:9$4
	if (!cell_i_display_24__3c__3c_EOT_3a_9_24_4) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time 0: clk=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " reg_bug=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<7> arg1;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = p_reg__bug.curr;
			formatter.arg0 = value<1>{0u};
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "<<EOT:9.9-9.61" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__3c__3c_EOT_3a_9_24_4 = value<1>{1u};
	}
	// \src: <<EOT:12.12-12.64
	// cell $display$<<EOT:12$6
	if (!cell_i_display_24__3c__3c_EOT_3a_12_24_6) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time 2: clk=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " reg_bug=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<7> arg1;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = p_reg__bug.curr;
			formatter.arg0 = value<1>{0u};
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "<<EOT:12.12-12.64" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__3c__3c_EOT_3a_12_24_6 = value<1>{1u};
	}
	// \src: <<EOT:11.9-11.61
	// cell $display$<<EOT:11$5
	if (!cell_i_display_24__3c__3c_EOT_3a_11_24_5) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time 1: clk=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " reg_bug=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<7> arg1;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = p_reg__bug.curr;
			formatter.arg0 = value<1>{0u};
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "<<EOT:11.9-11.61" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__3c__3c_EOT_3a_11_24_5 = value<1>{1u};
	}
	return converged;
}

void p_bug__debug::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_bug__debug::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "bug_debug", metadata_map({
			{ "top", UINT64_C(1) },
			{ "keep", UINT64_C(1) },
			{ "src", "<<EOT:1.1-14.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		static const value<1> const_p_clk = value<1>{0u};
		items->add(path, "clk", "src\000s<<EOT:3.9-3.12\000", const_p_clk);
		items->add(path, "reg_bug", "src\000s<<EOT:2.15-2.22\000", p_reg__bug, 0, debug_item::DRIVEN_SYNC);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_bug__debug>(new cxxrtl_design::p_bug__debug) };
}
