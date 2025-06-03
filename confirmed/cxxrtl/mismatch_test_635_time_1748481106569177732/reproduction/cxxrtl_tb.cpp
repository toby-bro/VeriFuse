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
// \src: bug.sv:1.1-11.10
struct p_bug : public module {
	// \src: bug.sv:2.15-2.22
	wire<7> p_reg__bug;
	// \src: bug.sv:3.9-3.12
	/*outline*/ value<1> p_clk;
	value<2> cell_i_assert_24_bug_2e_sv_3a_10_24_3;
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
	cell_i_assert_24_bug_2e_sv_3a_10_24_3 = {};
}

bool p_bug::eval(performer *performer) {
	bool converged = true;
	// cells $assert$bug.sv:10$3 $eq$bug.sv:10$4
	auto cell_i_assert_24_bug_2e_sv_3a_10_24_3_next = value<1>{0x1u}.concat(eq_uu<1>(p_reg__bug.curr, value<7>{0x1fu})).val();
	if (cell_i_assert_24_bug_2e_sv_3a_10_24_3 != cell_i_assert_24_bug_2e_sv_3a_10_24_3_next) {
		if (value<1>{0x1u}) {
			struct : public lazy_fmt {
				std::string operator() () const override {
					std::string buf;
					return buf;
				}
				struct performer *performer;
			} formatter;
			formatter.performer = performer;
			bool condition = (bool)eq_uu<1>(p_reg__bug.curr, value<7>{0x1fu});
			if (performer) {
				static const metadata_map attributes = metadata_map({
					{ "src", "bug.sv:10.17-10.46" },
				});
				performer->on_check(flavor::ASSERT, condition, formatter, attributes);
			} else {
				if (!condition) {
					std::cerr << formatter();
				}
				CXXRTL_ASSERT(condition && "Check failed");
			}
		}
		cell_i_assert_24_bug_2e_sv_3a_10_24_3 = cell_i_assert_24_bug_2e_sv_3a_10_24_3_next;
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
			{ "src", "bug.sv:1.1-11.10" },
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
