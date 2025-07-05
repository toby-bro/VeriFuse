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
	// \hdlname: split_if_only_then_inst_1751608204132_1007 out_reg_h
	// \src: ../simple_sub.sv:39.24-39.33
	wire<8> p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h;
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
	value<1> prev_p_inj__enable__pv__1751608204130__819;
	bool posedge_p_inj__enable__pv__1751608204130__819() const {
		return !prev_p_inj__enable__pv__1751608204130__819.slice<0>().val() && p_inj__enable__pv__1751608204130__819.slice<0>().val();
	}
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
	/*output*/ wire<8> p_inj__out1__z__1751608204148__329;
	// \src: ../simple_sub.sv:70.24-70.52
	/*output*/ wire<8> p_inj__out2__z__1751608204148__284;
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
	// \hdlname: CaseEq_inst_1751608204147_1101 match_z_eq
	// \src: ../simple_sub.sv:3.17-3.27
	/*outline*/ value<1> p_CaseEq__inst__1751608204147__1101_2e_match__z__eq;
	// \hdlname: CaseEq_inst_1751608204147_1101 match_x_neq
	// \src: ../simple_sub.sv:2.17-2.28
	/*outline*/ value<1> p_CaseEq__inst__1751608204147__1101_2e_match__x__neq;
	// \hdlname: case_parallel_simple_mod_inst_1751608204150_6962 internal_out
	// \src: ../simple_sub.sv:12.24-12.36
	/*outline*/ value<5> p_case__parallel__simple__mod__inst__1751608204150__6962_2e_internal__out;
	// \hdlname: module_ternary_inst_1751608204132_3568 out_ternary_result
	// \src: ../simple_sub.sv:28.24-28.42
	/*outline*/ value<8> p_module__ternary__inst__1751608204132__3568_2e_out__ternary__result;
	// \src: ../simple_sub.sv:81.18-81.41
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	/*outline*/ value<32> p_data__pv__ts1751608204131;
	p_simple__sub(interior) {}
	p_simple__sub() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		if (p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h.commit(observer)) changed = true;
		prev_p_inj__enable__pv__1751608204130__819 = p_inj__enable__pv__1751608204130__819;
		if (p_inj__out1__z__1751608204148__329.commit(observer)) changed = true;
		if (p_inj__out2__z__1751608204148__284.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();
	debug_outline debug_eval_outline { std::bind(&p_simple__sub::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_simple__sub

void p_simple__sub::reset() {
}

bool p_simple__sub::eval(performer *performer) {
	bool converged = true;
	bool posedge_p_inj__enable__pv__1751608204130__819 = this->posedge_p_inj__enable__pv__1751608204130__819();
	// \hdlname: CaseEq_inst_1751608204147_1101 data_io
	// \src: ../simple_sub.sv:4.22-4.29
	value<4> p_CaseEq__inst__1751608204147__1101_2e_data__io;
	// \hdlname: case_parallel_simple_mod_inst_1751608204150_6962 case_inside_val
	// \src: ../simple_sub.sv:11.23-11.38
	value<4> p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val;
	value<2> i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP;
	value<2> i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_114__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_117__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_120__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_123__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_126__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_129__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_18__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_21__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_24__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_27__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_30__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_33__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_36__Y;
	// \src: ../simple_sub.sv:120.49-120.86
	// \unused_bits: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
	value<32> i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_99__Y;
	// cells $add$../simple_sub.sv:120$18 $add$../simple_sub.sv:119$17 $add$../simple_sub.sv:118$16 $add$../simple_sub.sv:120$15 $add$../simple_sub.sv:119$14 $add$../simple_sub.sv:118$13
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_18__Y.slice<6,0>() = add_uu<7>(add_uu<6>(add_uu<5>(add_uu<4>(add_uu<3>(add_uu<2>(value<1>{0u}, p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// connection
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_18__Y.slice<7>() = value<1>{0u};
	// cells $add$../simple_sub.sv:120$21 $add$../simple_sub.sv:119$20 $add$../simple_sub.sv:118$19
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_21__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_18__Y.slice<6,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$24 $add$../simple_sub.sv:119$23 $add$../simple_sub.sv:118$22
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_24__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_21__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$27 $add$../simple_sub.sv:119$26 $add$../simple_sub.sv:118$25
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_27__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_24__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$30 $add$../simple_sub.sv:119$29 $add$../simple_sub.sv:118$28
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_30__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_27__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$33 $add$../simple_sub.sv:119$32 $add$../simple_sub.sv:118$31
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_33__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_30__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$36 $add$../simple_sub.sv:119$35 $add$../simple_sub.sv:118$34
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_36__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_33__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$99 $add$../simple_sub.sv:119$98 $add$../simple_sub.sv:118$97 $add$../simple_sub.sv:120$96 $add$../simple_sub.sv:119$95 $add$../simple_sub.sv:118$94 $add$../simple_sub.sv:120$93 $add$../simple_sub.sv:119$92 $add$../simple_sub.sv:118$91 $add$../simple_sub.sv:120$90 $add$../simple_sub.sv:119$89 $add$../simple_sub.sv:118$88 $add$../simple_sub.sv:120$87 $add$../simple_sub.sv:119$86 $add$../simple_sub.sv:118$85 $add$../simple_sub.sv:120$84 $add$../simple_sub.sv:119$83 $add$../simple_sub.sv:118$82 $add$../simple_sub.sv:120$81 $add$../simple_sub.sv:119$80 $add$../simple_sub.sv:118$79 $add$../simple_sub.sv:120$78 $add$../simple_sub.sv:119$77 $add$../simple_sub.sv:118$76 $add$../simple_sub.sv:120$75 $add$../simple_sub.sv:119$74 $add$../simple_sub.sv:118$73 $add$../simple_sub.sv:120$72 $add$../simple_sub.sv:119$71 $add$../simple_sub.sv:118$70 $add$../simple_sub.sv:120$69 $add$../simple_sub.sv:119$68 $add$../simple_sub.sv:118$67 $add$../simple_sub.sv:120$66 $add$../simple_sub.sv:119$65 $add$../simple_sub.sv:118$64 $add$../simple_sub.sv:120$63 $add$../simple_sub.sv:119$62 $add$../simple_sub.sv:118$61 $add$../simple_sub.sv:120$60 $add$../simple_sub.sv:119$59 $add$../simple_sub.sv:118$58 $add$../simple_sub.sv:120$57 $add$../simple_sub.sv:119$56 $add$../simple_sub.sv:118$55 $add$../simple_sub.sv:120$54 $add$../simple_sub.sv:119$53 $add$../simple_sub.sv:118$52 $add$../simple_sub.sv:120$51 $add$../simple_sub.sv:119$50 $add$../simple_sub.sv:118$49 $add$../simple_sub.sv:120$48 $add$../simple_sub.sv:119$47 $add$../simple_sub.sv:118$46 $add$../simple_sub.sv:120$45 $add$../simple_sub.sv:119$44 $add$../simple_sub.sv:118$43 $add$../simple_sub.sv:120$42 $add$../simple_sub.sv:119$41 $add$../simple_sub.sv:118$40 $add$../simple_sub.sv:120$39 $add$../simple_sub.sv:119$38 $add$../simple_sub.sv:118$37
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_99__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_36__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$114 $add$../simple_sub.sv:119$113 $add$../simple_sub.sv:118$112 $add$../simple_sub.sv:120$111 $add$../simple_sub.sv:119$110 $add$../simple_sub.sv:118$109 $add$../simple_sub.sv:120$108 $add$../simple_sub.sv:119$107 $add$../simple_sub.sv:118$106 $add$../simple_sub.sv:120$105 $add$../simple_sub.sv:119$104 $add$../simple_sub.sv:118$103 $add$../simple_sub.sv:120$102 $add$../simple_sub.sv:119$101 $add$../simple_sub.sv:118$100
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_114__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_99__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u}), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$117 $add$../simple_sub.sv:119$116 $add$../simple_sub.sv:118$115
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_117__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_114__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$120 $add$../simple_sub.sv:119$119 $add$../simple_sub.sv:118$118
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_120__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_117__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$123 $add$../simple_sub.sv:119$122 $add$../simple_sub.sv:118$121
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_123__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_120__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// cells $add$../simple_sub.sv:120$126 $add$../simple_sub.sv:119$125 $add$../simple_sub.sv:118$124
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_126__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_123__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// connection
	p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val = p_inj__data1__1751608204137__850;
	// cells $add$../simple_sub.sv:120$129 $add$../simple_sub.sv:119$128 $add$../simple_sub.sv:118$127
	i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_129__Y.slice<7,0>() = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_126__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_CMP0
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP.slice<0>() = eq_uu<1>(p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val, value<2>{0x2u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_CMP1
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP.slice<1>() = eq_uu<1>(p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val, value<2>{0x3u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_CMP1
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP.slice<1>() = eq_uu<1>(p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val, value<1>{0x1u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_CMP0
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP.slice<0>() = logic_not<1>(p_case__parallel__simple__mod__inst__1751608204150__6962_2e_case__inside__val);
	// connection
	p_CaseEq__inst__1751608204147__1101_2e_data__io = p_inj__data__io__1751608204147__331;
	// \full_case: 1
	// \src: ../simple_sub.sv:143.13-143.44|../simple_sub.sv:143.9-154.12
	// cell $procmux$149
	p_inj__data__out__pv__1751608204130__814 = (p_inj__enable__pv__1751608204130__819 ? p_a.slice<3,0>().val() : value<4>{0u});
	// \full_case: 1
	// \src: ../simple_sub.sv:143.13-143.44|../simple_sub.sv:143.9-154.12
	// cell $procmux$140
	p_inj__data__out__pa__1751608204130__355 = (p_inj__enable__pv__1751608204130__819 ? p_inj__data__in__pa__1751608204130__326.slice<7,0>().val() : value<8>{0u});
	// cells $add$../simple_sub.sv:120$132 $add$../simple_sub.sv:119$131 $add$../simple_sub.sv:118$130
	p_inj__large__sum__out__1751608204135__346 = add_uu<8>(add_uu<8>(add_uu<8>(i_add_24__2e__2e__2f_simple__sub_2e_sv_3a_120_24_129__Y.slice<7,0>().val(), p_inj__large__data__in__1751608204135__837.slice<0>().val()), p_inj__large__data__in__1751608204135__837.slice<1>().val()), value<1>{0x1u});
	// \src: ../simple_sub.sv:165.18-165.23
	// cell $sub$../simple_sub.sv:165$135
	p_sum = sub_uu<9>(p_a, p_a);
	// cells $procmux$155 $procmux$156_CMP0 $procmux$157_CMP0 $procmux$158_CMP0
	p_inj__data__out__case__1751608204137__757 = (eq_uu<1>(p_inj__large__data__in__1751608204135__837, value<2>{0x2u}) ? p_inj__data2__1751608204137__376 : (eq_uu<1>(p_inj__large__data__in__1751608204135__837, value<1>{0x1u}) ? p_inj__data1__1751608204137__850 : (logic_not<1>(p_inj__large__data__in__1751608204135__837) ? p_inj__data0__1751608204137__416 : p_inj__data3__1751608204137__768)));
	// cells $procdff$172 $procmux$160
	if (posedge_p_inj__enable__pv__1751608204130__819) {
		p_inj__out2__z__1751608204148__284.next = (p_inj__condition__h__1751608204132__423 ? p_inj__out2__z__1751608204148__284.curr : p_a);
	}
	// cells $procdff$171 $procmux$163
	if (posedge_p_inj__enable__pv__1751608204130__819) {
		p_inj__out1__z__1751608204148__329.next = (p_inj__condition__h__1751608204132__423 ? p_a : p_inj__out1__z__1751608204148__329.curr);
	}
	// cells $flatten\split_if_only_then_inst_1751608204132_1007.$procdff$173 $flatten\split_if_only_then_inst_1751608204132_1007.$procmux$165
	if (posedge_p_inj__enable__pv__1751608204130__819) {
		p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h.next = (p_inj__condition__h__1751608204132__423 ? p_a : p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h.curr);
	}
	// \src: ../simple_sub.sv:6.26-6.45
	// cell $flatten\CaseEq_inst_1751608204147_1101.$eqx$../simple_sub.sv:6$3
	p_inj__match__z__eq__1751608204147__256 = eqx_uu<1>(p_CaseEq__inst__1751608204147__1101_2e_data__io, value<4>{0xau});
	// \src: ../simple_sub.sv:7.27-7.46
	// cell $flatten\CaseEq_inst_1751608204147_1101.$nex$../simple_sub.sv:7$4
	p_inj__match__x__neq__1751608204147__458 = nex_uu<1>(p_CaseEq__inst__1751608204147__1101_2e_data__io, value<4>{0x8u});
	// cells $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$168 $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_ANY $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_ANY
	p_inj__internal__out__1751608204150__670 = (reduce_or<1>(i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP) ? value<5>{0xfu} : (reduce_or<1>(i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP) ? value<5>{0xeu} : value<5>{0x12u}));
	// \src: ../simple_sub.sv:31.26-31.61
	// cell $flatten\module_ternary_inst_1751608204132_3568.$ternary$../simple_sub.sv:31$7
	p_inj__out__ternary__result__1751608204132__418 = (p_inj__in__cond__ternary__1751608204132__347 ? p_inj__in__val1__1751608204132__518 : p_inj__in__val2__1751608204132__694);
	// connection
	p_inj__out__reg__h__1751608204132__733 = p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h.curr;
	// connection
	p_inj__out__1751608204133__79 = p_a.slice<3,0>().val();
	// connection
	p_inj__out__1751608204130__793 = p_a;
	// connection
	p_b = p_a;
	return converged;
}

void p_simple__sub::debug_eval() {
	value<2> i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP;
	value<2> i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP;
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_CMP0
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP.slice<0>() = eq_uu<1>(p_inj__data1__1751608204137__850, value<2>{0x2u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_CMP1
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP.slice<1>() = eq_uu<1>(p_inj__data1__1751608204137__850, value<2>{0x3u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_CMP1
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP.slice<1>() = eq_uu<1>(p_inj__data1__1751608204137__850, value<1>{0x1u});
	// \full_case: 1
	// \parallel: 1
	// \src: ../simple_sub.sv:0.0-0.0|../simple_sub.sv:16.9-20.16
	// cell $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_CMP0
	i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP.slice<0>() = logic_not<1>(p_inj__data1__1751608204137__850);
	// \src: ../simple_sub.sv:6.26-6.45
	// cell $flatten\CaseEq_inst_1751608204147_1101.$eqx$../simple_sub.sv:6$3
	p_CaseEq__inst__1751608204147__1101_2e_match__z__eq = eqx_uu<1>(p_inj__data__io__1751608204147__331, value<4>{0xau});
	// \src: ../simple_sub.sv:7.27-7.46
	// cell $flatten\CaseEq_inst_1751608204147_1101.$nex$../simple_sub.sv:7$4
	p_CaseEq__inst__1751608204147__1101_2e_match__x__neq = nex_uu<1>(p_inj__data__io__1751608204147__331, value<4>{0x8u});
	// cells $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$168 $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$169_ANY $flatten\case_parallel_simple_mod_inst_1751608204150_6962.$procmux$170_ANY
	p_case__parallel__simple__mod__inst__1751608204150__6962_2e_internal__out = (reduce_or<1>(i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_169__CMP) ? value<5>{0xfu} : (reduce_or<1>(i_flatten_5c_case__parallel__simple__mod__inst__1751608204150__6962_2e__24_procmux_24_170__CMP) ? value<5>{0xeu} : value<5>{0x12u}));
	// \src: ../simple_sub.sv:31.26-31.61
	// cell $flatten\module_ternary_inst_1751608204132_3568.$ternary$../simple_sub.sv:31$7
	p_module__ternary__inst__1751608204132__3568_2e_out__ternary__result = (p_inj__in__cond__ternary__1751608204132__347 ? p_inj__in__val1__1751608204132__518 : p_inj__in__val2__1751608204132__694);
	// connection
	p_data__pv__ts1751608204131.slice<7,0>() = value<4>{0u}.concat(p_inj__data__out__pv__1751608204130__814).val();
}

CXXRTL_EXTREMELY_COLD
void p_simple__sub::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "simple_sub", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../simple_sub.sv:48.1-166.10" },
		}), std::move(cell_attrs));
		scopes->add(path, "CaseEq_inst_1751608204147_1101", "CaseEq", "src\000s../simple_sub.sv:1.1-8.10\000", "src\000s../simple_sub.sv:99.12-103.6\000");
		scopes->add(path, "case_parallel_simple_mod_inst_1751608204150_6962", "case_parallel_simple_mod", "src\000s../simple_sub.sv:10.1-22.10\000", "src\000s../simple_sub.sv:85.30-88.6\000");
		scopes->add(path, "module_ternary_inst_1751608204132_3568", "module_ternary", "src\000s../simple_sub.sv:24.1-33.10\000", "src\000s../simple_sub.sv:136.20-141.6\000");
		scopes->add(path, "split_if_only_then_inst_1751608204132_1007", "split_if_only_then", "src\000s../simple_sub.sv:35.1-46.10\000", "src\000s../simple_sub.sv:130.24-135.6\000");
	}
	if (items) {
		items->add(path, "CaseEq_inst_1751608204147_1101 match_z_eq", "src\000s../simple_sub.sv:3.17-3.27\000", debug_eval_outline, p_CaseEq__inst__1751608204147__1101_2e_match__z__eq);
		items->add(path, "CaseEq_inst_1751608204147_1101 match_x_neq", "src\000s../simple_sub.sv:2.17-2.28\000", debug_eval_outline, p_CaseEq__inst__1751608204147__1101_2e_match__x__neq);
		items->add(path, "CaseEq_inst_1751608204147_1101 data_io", "src\000s../simple_sub.sv:4.22-4.29\000", debug_alias(), p_inj__data__io__1751608204147__331);
		items->add(path, "case_parallel_simple_mod_inst_1751608204150_6962 internal_out", "src\000s../simple_sub.sv:12.24-12.36\000", debug_eval_outline, p_case__parallel__simple__mod__inst__1751608204150__6962_2e_internal__out);
		items->add(path, "case_parallel_simple_mod_inst_1751608204150_6962 case_inside_val", "src\000s../simple_sub.sv:11.23-11.38\000", debug_alias(), p_inj__data1__1751608204137__850);
		items->add(path, "module_ternary_inst_1751608204132_3568 out_ternary_result", "src\000s../simple_sub.sv:28.24-28.42\000", debug_eval_outline, p_module__ternary__inst__1751608204132__3568_2e_out__ternary__result);
		items->add(path, "module_ternary_inst_1751608204132_3568 in_val2", "src\000s../simple_sub.sv:27.22-27.29\000", debug_alias(), p_inj__in__val2__1751608204132__694);
		items->add(path, "module_ternary_inst_1751608204132_3568 in_val1", "src\000s../simple_sub.sv:26.22-26.29\000", debug_alias(), p_inj__in__val1__1751608204132__518);
		items->add(path, "module_ternary_inst_1751608204132_3568 in_cond_ternary", "src\000s../simple_sub.sv:25.16-25.31\000", debug_alias(), p_inj__in__cond__ternary__1751608204132__347);
		items->add(path, "split_if_only_then_inst_1751608204132_1007 out_reg_h", "src\000s../simple_sub.sv:39.24-39.33\000", p_split__if__only__then__inst__1751608204132__1007_2e_out__reg__h, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "split_if_only_then_inst_1751608204132_1007 in_val_h", "src\000s../simple_sub.sv:38.23-38.31\000", debug_alias(), p_a);
		items->add(path, "split_if_only_then_inst_1751608204132_1007 condition_h", "src\000s../simple_sub.sv:37.17-37.28\000", debug_alias(), p_inj__condition__h__1751608204132__423);
		items->add(path, "split_if_only_then_inst_1751608204132_1007 clk_h", "src\000s../simple_sub.sv:36.17-36.22\000", debug_alias(), p_inj__enable__pv__1751608204130__819);
		items->add(path, "a", "src\000s../simple_sub.sv:49.23-49.24\000", p_a, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "b", "src\000s../simple_sub.sv:50.23-50.24\000", p_b, 0, debug_item::INPUT|debug_item::DRIVEN_COMB);
		items->add(path, "conflict_wire_ts1751608204130", "src\000s../simple_sub.sv:79.16-79.45\000", debug_alias(), p_a);
		items->add(path, "current_large_sum_ts1751608204136", "src\000s../simple_sub.sv:84.17-84.50\000", debug_alias(), p_inj__large__sum__out__1751608204135__346);
		items->add(path, "data_pa[0]", "src\000s../simple_sub.sv:82.17-82.24\000", debug_alias(), p_inj__data__out__pa__1751608204130__355);
		items->add(path, "data_pv_ts1751608204131", "src\000s../simple_sub.sv:81.18-81.41\000unused_bits\000s8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31\000", debug_eval_outline, p_data__pv__ts1751608204131);
		items->add(path, "inj_condition_h_1751608204132_423", "src\000s../simple_sub.sv:51.17-51.50\000", p_inj__condition__h__1751608204132__423, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data0_1751608204137_416", "src\000s../simple_sub.sv:52.23-52.50\000", p_inj__data0__1751608204137__416, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data1_1751608204137_850", "src\000s../simple_sub.sv:53.23-53.50\000", p_inj__data1__1751608204137__850, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data2_1751608204137_376", "src\000s../simple_sub.sv:54.23-54.50\000", p_inj__data2__1751608204137__376, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data3_1751608204137_768", "src\000s../simple_sub.sv:55.23-55.50\000", p_inj__data3__1751608204137__768, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_in_pa_1751608204130_326", "src\000s../simple_sub.sv:56.24-56.56\000", p_inj__data__in__pa__1751608204130__326, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_io_1751608204147_331", "src\000s../simple_sub.sv:76.22-76.51\000", p_inj__data__io__1751608204147__331, 0, debug_item::INOUT|debug_item::UNDRIVEN);
		items->add(path, "inj_data_out_case_1751608204137_757", "src\000s../simple_sub.sv:62.24-62.59\000", p_inj__data__out__case__1751608204137__757, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_data_out_pa_1751608204130_355", "src\000s../simple_sub.sv:63.24-63.57\000", p_inj__data__out__pa__1751608204130__355, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_data_out_pv_1751608204130_814", "src\000s../simple_sub.sv:64.24-64.57\000", p_inj__data__out__pv__1751608204130__814, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_enable_pv_1751608204130_819", "src\000s../simple_sub.sv:57.17-57.48\000", p_inj__enable__pv__1751608204130__819, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_cond_ternary_1751608204132_347", "src\000s../simple_sub.sv:58.16-58.53\000", p_inj__in__cond__ternary__1751608204132__347, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_val1_1751608204132_518", "src\000s../simple_sub.sv:59.22-59.51\000", p_inj__in__val1__1751608204132__518, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_in_val2_1751608204132_694", "src\000s../simple_sub.sv:60.22-60.51\000", p_inj__in__val2__1751608204132__694, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_internal_out_1751608204150_670", "src\000s../simple_sub.sv:65.24-65.58\000", p_inj__internal__out__1751608204150__670, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_large_data_in_1751608204135_837", "src\000s../simple_sub.sv:61.23-61.58\000", p_inj__large__data__in__1751608204135__837, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_large_sum_out_1751608204135_346", "src\000s../simple_sub.sv:66.24-66.59\000", p_inj__large__sum__out__1751608204135__346, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_match_x_neq_1751608204147_458", "src\000s../simple_sub.sv:67.17-67.50\000", p_inj__match__x__neq__1751608204147__458, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_match_z_eq_1751608204147_256", "src\000s../simple_sub.sv:68.17-68.49\000", p_inj__match__z__eq__1751608204147__256, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out1_z_1751608204148_329", "src\000s../simple_sub.sv:69.24-69.52\000", p_inj__out1__z__1751608204148__329, 0, debug_item::OUTPUT|debug_item::DRIVEN_SYNC);
		items->add(path, "inj_out2_z_1751608204148_284", "src\000s../simple_sub.sv:70.24-70.52\000", p_inj__out2__z__1751608204148__284, 0, debug_item::OUTPUT|debug_item::DRIVEN_SYNC);
		items->add(path, "inj_out_1751608204130_793", "src\000s../simple_sub.sv:71.24-71.49\000", p_inj__out__1751608204130__793, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out_1751608204133_79", "src\000s../simple_sub.sv:72.24-72.48\000", p_inj__out__1751608204133__79, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out_reg_h_1751608204132_733", "src\000s../simple_sub.sv:73.24-73.55\000", p_inj__out__reg__h__1751608204132__733, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "inj_out_ternary_result_1751608204132_418", "src\000s../simple_sub.sv:74.24-74.64\000", p_inj__out__ternary__result__1751608204132__418, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "sum", "src\000s../simple_sub.sv:75.24-75.27\000", p_sum, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_simple__sub>(new cxxrtl_design::p_simple__sub) };
}
