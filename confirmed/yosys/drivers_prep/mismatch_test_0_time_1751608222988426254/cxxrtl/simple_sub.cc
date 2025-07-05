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
// \src: ../simple_sub.sv:48.1-166.10
struct p_simple__sub : public module {
	// \src: ../simple_sub.sv:49.23-49.24
	/*input*/ value<8> p_a;
	// \src: ../simple_sub.sv:50.23-50.24
	/*input*/ value<8> p_b;
	// \src: ../simple_sub.sv:51.17-51.50
	/*input*/ value<1> p_inj__condition__h__1751608204132__423;
	// \src: ../simple_sub.sv:52.23-52.50
	/*input*/ value<4> p_inj__data0__1751608204137__416;
	// \src: ../simple_sub.sv:53.23-53.50
	/*input*/ value<4> p_inj__data1__1751608204137__850;
	// \src: ../simple_sub.sv:54.23-54.50
	/*input*/ value<4> p_inj__data2__1751608204137__376;
	// \src: ../simple_sub.sv:55.23-55.50
	/*input*/ value<4> p_inj__data3__1751608204137__768;
	// \src: ../simple_sub.sv:56.24-56.56
	/*input*/ value<16> p_inj__data__in__pa__1751608204130__326;
	// \src: ../simple_sub.sv:76.22-76.51
	/*inout*/ value<4> p_inj__data__io__1751608204147__331;
	// \src: ../simple_sub.sv:62.24-62.59
	/*output*/ value<4> p_inj__data__out__case__1751608204137__757;
	// \src: ../simple_sub.sv:63.24-63.57
	/*output*/ value<8> p_inj__data__out__pa__1751608204130__355;
	// \src: ../simple_sub.sv:64.24-64.57
	/*output*/ value<4> p_inj__data__out__pv__1751608204130__814;
	// \src: ../simple_sub.sv:57.17-57.48
	/*input*/ value<1> p_inj__enable__pv__1751608204130__819;
	// \src: ../simple_sub.sv:58.16-58.53
	/*input*/ value<1> p_inj__in__cond__ternary__1751608204132__347;
	// \src: ../simple_sub.sv:59.22-59.51
	/*input*/ value<8> p_inj__in__val1__1751608204132__518;
	// \src: ../simple_sub.sv:60.22-60.51
	/*input*/ value<8> p_inj__in__val2__1751608204132__694;
	// \src: ../simple_sub.sv:65.24-65.58
	/*output*/ value<5> p_inj__internal__out__1751608204150__670;
	// \src: ../simple_sub.sv:61.23-61.58
	/*input*/ value<2> p_inj__large__data__in__1751608204135__837;
	// \src: ../simple_sub.sv:66.24-66.59
	/*output*/ value<8> p_inj__large__sum__out__1751608204135__346;
	// \src: ../simple_sub.sv:67.17-67.50
	/*output*/ value<1> p_inj__match__x__neq__1751608204147__458;
	// \src: ../simple_sub.sv:68.17-68.49
	/*output*/ value<1> p_inj__match__z__eq__1751608204147__256;
	// \src: ../simple_sub.sv:69.24-69.52
	/*output*/ value<8> p_inj__out1__z__1751608204148__329;
	// \src: ../simple_sub.sv:70.24-70.52
	/*output*/ value<8> p_inj__out2__z__1751608204148__284;
	// \src: ../simple_sub.sv:71.24-71.49
	/*output*/ value<8> p_inj__out__1751608204130__793;
	// \src: ../simple_sub.sv:72.24-72.48
	/*output*/ value<4> p_inj__out__1751608204133__79;
	// \src: ../simple_sub.sv:73.24-73.55
	/*output*/ value<8> p_inj__out__reg__h__1751608204132__733;
	// \src: ../simple_sub.sv:74.24-74.64
	/*output*/ value<8> p_inj__out__ternary__result__1751608204132__418;
	// \src: ../simple_sub.sv:75.24-75.27
	/*output*/ value<9> p_sum;
	p_simple__sub(interior) {}
	p_simple__sub() {
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
}; // struct p_simple__sub

void p_simple__sub::reset() {
}

bool p_simple__sub::eval(performer *performer) {
	bool converged = true;
	// \src: ../simple_sub.sv:165.18-165.23
	// cell $sub$../simple_sub.sv:165$7
	p_sum = sub_uu<9>(p_a, p_a);
	// connection
	p_inj__out__1751608204130__793 = p_a;
	// connection
	p_b = p_a;
	return converged;
}

void p_simple__sub::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_simple__sub::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "simple_sub", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../simple_sub.sv:48.1-166.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "a", "src\000s../simple_sub.sv:49.23-49.24\000", p_a, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "b", "src\000s../simple_sub.sv:50.23-50.24\000", p_b, 0, debug_item::INPUT|debug_item::DRIVEN_COMB);
		items->add(path, "conflict_wire_ts1751608204130", "src\000s../simple_sub.sv:79.16-79.45\000", debug_alias(), p_a);
		items->add(path, "inj_condition_h_1751608204132_423", "src\000s../simple_sub.sv:51.17-51.50\000", p_inj__condition__h__1751608204132__423, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data0_1751608204137_416", "src\000s../simple_sub.sv:52.23-52.50\000", p_inj__data0__1751608204137__416, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data1_1751608204137_850", "src\000s../simple_sub.sv:53.23-53.50\000", p_inj__data1__1751608204137__850, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data2_1751608204137_376", "src\000s../simple_sub.sv:54.23-54.50\000", p_inj__data2__1751608204137__376, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data3_1751608204137_768", "src\000s../simple_sub.sv:55.23-55.50\000", p_inj__data3__1751608204137__768, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_in_pa_1751608204130_326", "src\000s../simple_sub.sv:56.24-56.56\000", p_inj__data__in__pa__1751608204130__326, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_io_1751608204147_331", "src\000s../simple_sub.sv:76.22-76.51\000", p_inj__data__io__1751608204147__331, 0, debug_item::INOUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_out_case_1751608204137_757", "src\000s../simple_sub.sv:62.24-62.59\000", p_inj__data__out__case__1751608204137__757, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_out_pa_1751608204130_355", "src\000s../simple_sub.sv:63.24-63.57\000", p_inj__data__out__pa__1751608204130__355, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_out_pv_1751608204130_814", "src\000s../simple_sub.sv:64.24-64.57\000", p_inj__data__out__pv__1751608204130__814, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_enable_pv_1751608204130_819", "src\000s../simple_sub.sv:57.17-57.48\000", p_inj__enable__pv__1751608204130__819, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_cond_ternary_1751608204132_347", "src\000s../simple_sub.sv:58.16-58.53\000", p_inj__in__cond__ternary__1751608204132__347, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_val1_1751608204132_518", "src\000s../simple_sub.sv:59.22-59.51\000", p_inj__in__val1__1751608204132__518, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_val2_1751608204132_694", "src\000s../simple_sub.sv:60.22-60.51\000", p_inj__in__val2__1751608204132__694, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_internal_out_1751608204150_670", "src\000s../simple_sub.sv:65.24-65.58\000", p_inj__internal__out__1751608204150__670, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_large_data_in_1751608204135_837", "src\000s../simple_sub.sv:61.23-61.58\000", p_inj__large__data__in__1751608204135__837, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_large_sum_out_1751608204135_346", "src\000s../simple_sub.sv:66.24-66.59\000", p_inj__large__sum__out__1751608204135__346, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_match_x_neq_1751608204147_458", "src\000s../simple_sub.sv:67.17-67.50\000", p_inj__match__x__neq__1751608204147__458, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_match_z_eq_1751608204147_256", "src\000s../simple_sub.sv:68.17-68.49\000", p_inj__match__z__eq__1751608204147__256, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out1_z_1751608204148_329", "src\000s../simple_sub.sv:69.24-69.52\000", p_inj__out1__z__1751608204148__329, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out2_z_1751608204148_284", "src\000s../simple_sub.sv:70.24-70.52\000", p_inj__out2__z__1751608204148__284, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out_1751608204130_793", "src\000s../simple_sub.sv:71.24-71.49\000", p_inj__out__1751608204130__793, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out_1751608204133_79", "src\000s../simple_sub.sv:72.24-72.48\000", p_inj__out__1751608204133__79, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out_reg_h_1751608204132_733", "src\000s../simple_sub.sv:73.24-73.55\000", p_inj__out__reg__h__1751608204132__733, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_out_ternary_result_1751608204132_418", "src\000s../simple_sub.sv:74.24-74.64\000", p_inj__out__ternary__result__1751608204132__418, 0, debug_item::OUTPUT|debug_item::UNDRIVEN);
		items->add(path, "sum", "src\000s../simple_sub.sv:75.24-75.27\000", p_sum, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_simple__sub>(new cxxrtl_design::p_simple__sub) };
}
