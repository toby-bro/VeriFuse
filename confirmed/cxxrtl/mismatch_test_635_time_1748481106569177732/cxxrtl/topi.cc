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
// \src: ../top_100.sv:4.1-76.10
struct p_topi : public module {
	// \src: ../top_100.sv:11.15-11.19
	wire<7> p___11__;
	// \src: ../top_100.sv:17.18-17.28
	/*input*/ value<96> p_clkin__data;
	// \src: ../top_100.sv:18.19-18.26
	/*input*/ value<192> p_in__data;
	// \src: ../top_100.sv:20.23-20.40
	/*output*/ value<8> p_inj__param__out__547;
	// \src: ../top_100.sv:19.20-19.28
	/*output*/ value<192> p_out__data;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_44_24_22;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_45_24_23;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_46_24_24;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_48_24_26;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_50_24_29;
	value<144> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4;
	value<250> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9;
	value<2> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13;
	value<9> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17;
	value<1> cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19;
	p_topi(interior) {}
	p_topi() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		if (p___11__.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_topi

void p_topi::reset() {
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_44_24_22 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_45_24_23 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_46_24_24 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_48_24_26 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_50_24_29 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17 = {};
	cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19 = {};
}

bool p_topi::eval(performer *performer) {
	bool converged = true;
	// \src: ../top_100.sv:29.5-33.60
	value<7> i_0_5c___11___5b_6_3a_0_5d_;
	// \src: ../top_100.sv:55.18-55.79
	value<136> i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_41;
	// \src: ../top_100.sv:70.13-70.45
	value<1> i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y;
	// \src: ../top_100.sv:70.13-70.45
	// cell $eq$../top_100.sv:70$16
	i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y = logic_not<1>(value<1>{0u}.concat(p___11__.curr).val());
	// \src: ../top_100.sv:33.40-33.56
	// cell $reduce_or$../top_100.sv:33$2
	i_0_5c___11___5b_6_3a_0_5d_.slice<0>() = reduce_or<1>(p_in__data.slice<84,76>().val());
	// connection
	i_0_5c___11___5b_6_3a_0_5d_.slice<6,1>() = p_in__data.slice<48,43>().val();
	// cells $ternary$../top_100.sv:55$7 $eq$../top_100.sv:55$5
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_41.slice<134,0>() = (logic_not<1>(p___11__.curr) ? value<135>{0x45534554u,0x41542052u,0x55434b20u,0x5354u,0u} : value<135>{0x43544c59u,0x4f525245u,0x45442043u,0x50444154u,0x55u});
	// connection
	i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_41.slice<135>() = value<1>{0u};
	// \always_ff: 1
	// \src: ../top_100.sv:29.5-33.60
	// cell $procdff$40
	if (p_clkin__data.slice<32>().val() == value<1> {1u}) {
		p___11__.next = value<7>{0u};
	}
	// cells $display$../top_100.sv:73$19 $procmux$33 $procmux$30 $eq$../top_100.sv:72$18
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19_next = (i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y ? value<1>{0u} : (eq_uu<1>(p___11__.curr, value<5>{0x1fu}) ? value<1>{0x1u} : value<1>{0u})).concat(value<0>()).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19_next) {
		if ((i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y ? value<1>{0u} : (eq_uu<1>(p___11__.curr, value<5>{0x1fu}) ? value<1>{0x1u} : value<1>{0u}))) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, ">>> CORRECT: Register updated on negedge!\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
			} formatter;
			formatter.performer = performer;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:73.13-73.67" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_73_24_19_next;
	}
	// cells $display$../top_100.sv:71$17 $procmux$36
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17_next = (i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y ? value<1>{0x1u} : value<1>{0u}).concat(value<0>()).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17_next) {
		if ((i_eq_24__2e__2e__2f_top__100_2e_sv_3a_70_24_16__Y ? value<1>{0x1u} : value<1>{0u})) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, ">>> CXXRTL BUG: Register stuck at reset value!\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
			} formatter;
			formatter.performer = performer;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:71.13-71.72" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_71_24_17_next;
	}
	// \src: ../top_100.sv:69.9-69.80
	// cell $display$../top_100.sv:69$15
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15_next = value<1>{0x1u}.concat(value<1>{0u}.concat(p___11__.curr).val()).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15_next) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::VLOG_TIME, "", fmt_part::NUMERIC, (char)48, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::LITERAL, ": inj_param_out_547 = ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 8, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<8> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg0 = value<1>{0u}.concat(p___11__.curr).val();
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:69.9-69.80" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_69_24_15_next;
	}
	// \src: ../top_100.sv:64.9-64.65
	// cell $display$../top_100.sv:64$13
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13_next = value<1>{0x1u}.concat(p_clkin__data.slice<32>().val()).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13_next) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::VLOG_TIME, "", fmt_part::NUMERIC, (char)48, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::LITERAL, ": reset = ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg0 = p_clkin__data.slice<32>().val();
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:64.9-64.65" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_64_24_13_next;
	}
	// \src: ../top_100.sv:59.9-60.73
	// cell $display$../top_100.sv:59$9
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9_next = value<1>{0x1u}.concat(value<249>{0x6262be52u,0xcae440beu,0xe4d2ceceu,0xd8c840e8u,0xe6d0deeau,0xca405a40u,0xcecac8ceu,0x50dccau}).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9_next) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::VLOG_TIME, "", fmt_part::NUMERIC, (char)48, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::LITERAL, ": simple_clock = ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::STRING, "", fmt_part::RIGHT, (char)32, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<248> arg1;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = value<248>{0x31315f29u,0x6572205fu,0x72696767u,0x6c642074u,0x73686f75u,0x65202d20u,0x67656467u,0x286e65u};
			formatter.arg0 = value<1>{0u};
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:59.9-60.73" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_59_24_9_next;
	}
	// \src: ../top_100.sv:54.9-55.81
	// cell $display$../top_100.sv:54$4
	auto cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4_next = value<1>{0x1u}.concat(value<1>{0u}.concat(i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_41.slice<134,0>()).concat(p___11__.curr).val()).val();
	if (cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4 != cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4_next) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Time ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::VLOG_TIME, "", fmt_part::NUMERIC, (char)48, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::LITERAL, ": _11_ = ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, " (", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::STRING, "", fmt_part::RIGHT, (char)32, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, ")\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<136> arg1;
				value<7> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = value<1>{0u}.concat(i_auto_24_wreduce_2e_cc_3a_514_3a_run_24_41.slice<134,0>()).val();
			formatter.arg0 = p___11__.curr;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:54.9-55.81" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4 = cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_54_24_4_next;
	}
	// \src: ../top_100.sv:50.9-50.79
	// cell $display$../top_100.sv:50$29
	if (!cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_50_24_29) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Testing: always_ff @(negedge simple_clock, posedge reset)\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
			} formatter;
			formatter.performer = performer;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:50.9-50.79" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_50_24_29 = value<1>{1u};
	}
	// \src: ../top_100.sv:48.9-49.92
	// cell $display$../top_100.sv:48$26
	if (!cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_48_24_26) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Expected _11_ update: {", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 6, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, ", ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "} = ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 7, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg2, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<7> arg2;
				value<1> arg1;
				value<6> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg2 = p_in__data.slice<48,43>().concat(i_0_5c___11___5b_6_3a_0_5d_.slice<0>()).val();
			formatter.arg1 = i_0_5c___11___5b_6_3a_0_5d_.slice<0>().val();
			formatter.arg0 = p_in__data.slice<48,43>().val();
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:48.9-49.92" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_48_24_26 = value<1>{1u};
	}
	// \src: ../top_100.sv:46.9-47.54
	// cell $display$../top_100.sv:46$24
	if (!cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_46_24_24) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Expected data: in_data[48:43]=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 6, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, ", |in_data[84:76]=", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg1, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<1> arg1;
				value<6> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg1 = i_0_5c___11___5b_6_3a_0_5d_.slice<0>().val();
			formatter.arg0 = p_in__data.slice<48,43>().val();
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:46.9-47.54" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_46_24_24 = value<1>{1u};
	}
	// \src: ../top_100.sv:45.9-45.64
	// cell $display$../top_100.sv:45$23
	if (!cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_45_24_23) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "Reset (clkin_data[32]): ", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					buf += fmt_part { fmt_part::INTEGER, "", fmt_part::RIGHT, (char)48, 1, 2, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(arg0, performer);
					buf += fmt_part { fmt_part::LITERAL, "\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
				value<1> arg0;
			} formatter;
			formatter.performer = performer;
			formatter.arg0 = p_clkin__data.slice<32>().val();
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:45.9-45.64" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_45_24_23 = value<1>{1u};
	}
	// \src: ../top_100.sv:44.9-44.67
	// cell $display$../top_100.sv:44$22
	if (!cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_44_24_22) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					buf += fmt_part { fmt_part::LITERAL, "=== ULTRA-MINIMAL CXXRTL NEGEDGE BUG TEST ===\012", fmt_part::RIGHT, (char)0, 0, 10, 0, fmt_part::MINUS, 0, 0, 0, 0 }.render(value<0>(), performer);
					return buf;
				}
				struct performer *performer;
			} formatter;
			formatter.performer = performer;
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "../top_100.sv:44.9-44.67" },
				});
				performer->on_print(formatter, attributes);
			} else {
				std::cout << formatter();
			}
		}
		cell_i_display_24__2e__2e__2f_top__100_2e_sv_3a_44_24_22 = value<1>{1u};
	}
	// connection
	p_out__data = value<192>{0u,0u,0u,0u,0u,0u};
	// connection
	p_inj__param__out__547 = value<1>{0u}.concat(p___11__.curr).val();
	return converged;
}

void p_topi::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_topi::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "topi", metadata_map({
			{ "keep", UINT64_C(1) },
			{ "top", UINT64_C(1) },
			{ "src", "../top_100.sv:4.1-76.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "_11_", "src\000s../top_100.sv:11.15-11.19\000", p___11__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "clkin_data", "src\000s../top_100.sv:17.18-17.28\000", p_clkin__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "in_data", "src\000s../top_100.sv:18.19-18.26\000", p_in__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_param_out_547", "src\000s../top_100.sv:20.23-20.40\000", p_inj__param__out__547, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "out_data", "src\000s../top_100.sv:19.20-19.28\000", p_out__data, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		static const value<1> const_p_simple__clock = value<1>{0u};
		items->add(path, "simple_clock", "src\000s../top_100.sv:14.9-14.21\000", const_p_simple__clock);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_topi>(new cxxrtl_design::p_topi) };
}
