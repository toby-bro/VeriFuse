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
// \src: ../top_100.sv:10.1-100.10
struct p_topi : public module {
	// \src: ../top_100.sv:17.18-17.22
	wire<12> p___01__;
	// \src: ../top_100.sv:18.17-18.21
	wire<5> p___02__;
	// \src: ../top_100.sv:68.17-68.21
	wire<7> p___11__;
	// \src: ../top_100.sv:42.12-42.28
	value<1> p_celloutsig__1__19z;
	value<1> prev_p_celloutsig__1__19z;
	bool negedge_p_celloutsig__1__19z() const {
		return prev_p_celloutsig__1__19z.slice<0>().val() && !p_celloutsig__1__19z.slice<0>().val();
	}
	// \src: ../top_100.sv:48.20-48.30
	/*input*/ value<96> p_clkin__data;
	value<96> prev_p_clkin__data;
	bool posedge_p_clkin__data_0() const {
		return !prev_p_clkin__data.slice<0>().val() && p_clkin__data.slice<0>().val();
	}
	// \src: ../top_100.sv:50.21-50.28
	/*input*/ value<192> p_in__data;
	// \src: ../top_100.sv:54.23-54.40
	/*output*/ value<8> p_inj__param__out__547;
	// \src: ../top_100.sv:52.22-52.30
	/*output*/ value<192> p_out__data;
	// \src: ../top_100.sv:20.12-20.27
	/*outline*/ value<1> p_celloutsig__0__0z;
	// \src: ../top_100.sv:21.12-21.28
	/*outline*/ value<1> p_celloutsig__0__11z;
	/*outline*/ value<3> p_celloutsig__0__12z;
	// \src: ../top_100.sv:23.18-23.34
	/*outline*/ value<7> p_celloutsig__0__13z;
	// \src: ../top_100.sv:24.12-24.28
	/*outline*/ value<1> p_celloutsig__0__15z;
	// \src: ../top_100.sv:25.12-25.28
	/*outline*/ value<1> p_celloutsig__0__16z;
	// \src: ../top_100.sv:26.12-26.28
	/*outline*/ value<1> p_celloutsig__0__17z;
	// \src: ../top_100.sv:27.18-27.34
	// \unused_bits: 2
	/*outline*/ value<6> p_celloutsig__0__19z;
	// \src: ../top_100.sv:28.12-28.28
	/*outline*/ value<1> p_celloutsig__0__25z;
	// \src: ../top_100.sv:29.12-29.28
	/*outline*/ value<1> p_celloutsig__0__26z;
	// \src: ../top_100.sv:30.12-30.27
	/*outline*/ value<1> p_celloutsig__0__2z;
	// \src: ../top_100.sv:31.12-31.27
	/*outline*/ value<1> p_celloutsig__0__3z;
	// \src: ../top_100.sv:32.12-32.27
	/*outline*/ value<1> p_celloutsig__0__4z;
	// \src: ../top_100.sv:33.12-33.27
	/*outline*/ value<1> p_celloutsig__0__6z;
	// \unused_bits: 2
	/*outline*/ value<9> p_celloutsig__0__7z;
	// \src: ../top_100.sv:35.18-35.33
	/*outline*/ value<8> p_celloutsig__0__8z;
	// \src: ../top_100.sv:36.19-36.34
	// \unused_bits: 1 2 3 4 5 6 7 8 9 10 11 12
	/*outline*/ value<13> p_celloutsig__0__9z;
	// \src: ../top_100.sv:37.12-37.27
	/*outline*/ value<1> p_celloutsig__1__0z;
	// \src: ../top_100.sv:39.12-39.28
	/*outline*/ value<1> p_celloutsig__1__12z;
	// \src: ../top_100.sv:40.12-40.28
	/*outline*/ value<1> p_celloutsig__1__14z;
	// \src: ../top_100.sv:41.12-41.28
	/*outline*/ value<1> p_celloutsig__1__18z;
	// \src: ../top_100.sv:43.18-43.33
	/*outline*/ value<4> p_celloutsig__1__1z;
	// \src: ../top_100.sv:44.18-44.33
	/*outline*/ value<6> p_celloutsig__1__2z;
	// \src: ../top_100.sv:45.12-45.27
	/*outline*/ value<1> p_celloutsig__1__3z;
	// \src: ../top_100.sv:46.12-46.27
	/*outline*/ value<1> p_celloutsig__1__4z;
	// \src: ../top_100.sv:47.19-47.34
	// \unused_bits: 0 1 2 3 4 5 6 7
	/*outline*/ value<12> p_celloutsig__1__9z;
	p_topi(interior) {}
	p_topi() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		if (p___01__.commit(observer)) changed = true;
		if (p___02__.commit(observer)) changed = true;
		if (p___11__.commit(observer)) changed = true;
		prev_p_celloutsig__1__19z = p_celloutsig__1__19z;
		prev_p_clkin__data = p_clkin__data;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();
	debug_outline debug_eval_outline { std::bind(&p_topi::debug_eval, this) };

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_topi

void p_topi::reset() {
}

bool p_topi::eval(performer *performer) {
	bool converged = true;
	bool negedge_p_celloutsig__1__19z = this->negedge_p_celloutsig__1__19z();
	bool posedge_p_clkin__data_0 = this->posedge_p_clkin__data_0();
	// \src: ../top_100.sv:20.12-20.27
	value<1> p_celloutsig__0__0z;
	value<3> p_celloutsig__0__12z;
	// \src: ../top_100.sv:23.18-23.34
	value<7> p_celloutsig__0__13z;
	// \src: ../top_100.sv:25.12-25.28
	value<1> p_celloutsig__0__16z;
	// \src: ../top_100.sv:27.18-27.34
	// \unused_bits: 2
	value<6> p_celloutsig__0__19z;
	// \src: ../top_100.sv:30.12-30.27
	value<1> p_celloutsig__0__2z;
	// \src: ../top_100.sv:31.12-31.27
	value<1> p_celloutsig__0__3z;
	// \src: ../top_100.sv:32.12-32.27
	value<1> p_celloutsig__0__4z;
	// \unused_bits: 2
	value<9> p_celloutsig__0__7z;
	// \src: ../top_100.sv:35.18-35.33
	value<8> p_celloutsig__0__8z;
	// \src: ../top_100.sv:37.12-37.27
	value<1> p_celloutsig__1__0z;
	// \src: ../top_100.sv:39.12-39.28
	value<1> p_celloutsig__1__12z;
	// \src: ../top_100.sv:43.18-43.33
	value<4> p_celloutsig__1__1z;
	// \src: ../top_100.sv:44.18-44.33
	value<6> p_celloutsig__1__2z;
	// \src: ../top_100.sv:46.12-46.27
	value<1> p_celloutsig__1__4z;
	// \src: ../top_100.sv:85.32-85.48
	// cell $reduce_or$../top_100.sv:85$25
	p_celloutsig__0__0z = reduce_or<1>(p_in__data.slice<84,76>().val());
	// cells $logic_not$../top_100.sv:60$4 $ternary$../top_100.sv:60$3
	p_celloutsig__0__2z = logic_not<1>((p_celloutsig__0__0z ? value<1>{0x1u} : p_in__data.slice<47>().val()));
	// \src: ../top_100.sv:91.32-91.94
	// cell $reduce_or$../top_100.sv:91$31
	p_celloutsig__0__3z = reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__2z).val());
	// \src: ../top_100.sv:79.32-79.254
	// cell $eqx$../top_100.sv:79$19
	p_celloutsig__0__4z = eqx_uu<1>(p_celloutsig__0__3z.concat(p_celloutsig__0__2z).concat(p_celloutsig__0__3z.repeat<2>()).concat(p_celloutsig__0__2z).concat(p_celloutsig__0__0z.repeat<2>()).concat(p_celloutsig__0__2z.repeat<2>()).val(), p_celloutsig__0__2z.concat(p___11__.curr).concat(p_celloutsig__0__0z).val());
	// \src: ../top_100.sv:64.32-64.59
	// cell $xor$../top_100.sv:64$11
	p_celloutsig__1__0z = xor_uu<1>(p_in__data.slice<144>().val(), p_in__data.slice<107>().val());
	// \src: ../top_100.sv:96.32-96.143
	// cell $xnor$../top_100.sv:96$36
	p_celloutsig__0__8z = xnor_uu<8>(p_celloutsig__0__4z.concat(p___11__.curr).val(), p___11__.curr.slice<5,0>().concat(p_celloutsig__0__3z.repeat<2>()).val());
	// \src: ../top_100.sv:84.32-84.145
	// cell $or$../top_100.sv:84$24
	p_celloutsig__0__7z = or_uu<9>(p_in__data.slice<82,74>().val(), p___11__.curr.slice<4,0>().concat(p_celloutsig__0__2z).concat(p_celloutsig__0__3z.repeat<2>()).concat(p_celloutsig__0__2z).val());
	// \src: ../top_100.sv:77.32-77.115
	// cell $div$../top_100.sv:77$17
	p_celloutsig__1__1z = div_uu<4>(p_in__data.slice<168,167>().concat(p_celloutsig__1__0z.repeat<2>()).val(), value<1>{0x1u}.concat(p_in__data.slice<126,124>()).val());
	// \src: ../top_100.sv:95.32-95.125
	// cell $sshl$../top_100.sv:95$35
	p_celloutsig__1__2z = sshl_uu<6>(p_celloutsig__1__1z.concat(p_celloutsig__1__0z.repeat<2>()).val(), p_in__data.slice<97,96>().concat(p_celloutsig__1__1z).val());
	// \src: ../top_100.sv:90.32-90.75
	// cell $reduce_or$../top_100.sv:90$30
	p_celloutsig__1__4z = reduce_or<1>(p_celloutsig__1__2z.slice<5,3>().concat(p_celloutsig__1__0z).val());
	// cells $sshl$../top_100.sv:94$34 $reduce_or$../top_100.sv:88$28
	p_celloutsig__0__12z = sshl_uu<3>(p_celloutsig__0__7z.slice<7,5>().concat(reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__4z).concat(p_celloutsig__0__2z).val())).val(), p_in__data.slice<81,78>().val());
	// cells $reduce_or$../top_100.sv:87$27 $sshl$../top_100.sv:93$33
	p_celloutsig__1__12z = reduce_or<1>(sshl_uu<12>(p_celloutsig__1__4z.concat(p_celloutsig__1__1z).concat(p_celloutsig__1__2z).concat(p_celloutsig__1__0z).val(), p_in__data.slice<130,119>().val()).slice<11,8>().concat(p_celloutsig__1__2z.slice<5,3>()).concat(p_celloutsig__1__0z).concat(p___02__.curr).concat(p___01__.curr.slice<10,0>()).val());
	// \src: ../top_100.sv:82.33-82.99
	// cell $ne$../top_100.sv:82$22
	p_celloutsig__0__16z = ne_uu<1>(p_celloutsig__0__7z.slice<1,0>().concat(p_celloutsig__0__2z).val(), p_celloutsig__0__12z);
	// cells $div$../top_100.sv:78$18 $not$../top_100.sv:61$7 $and$../top_100.sv:61$6 $or$../top_100.sv:61$5 $div$../top_100.sv:76$16
	p_celloutsig__0__13z = div_uu<7>(p_in__data.slice<30,24>().val(), value<1>{0x1u}.concat(p_celloutsig__0__7z.slice<8,4>()).concat(not_u<1>(and_uu<1>(or_uu<1>(div_uu<13>(p_in__data.slice<26,21>().concat(p___11__.curr).val(), value<1>{0x1u}.concat(p_celloutsig__0__7z.slice<5,3>()).concat(p_celloutsig__0__8z).concat(p_celloutsig__0__0z).val()).slice<0>().val(), p_in__data.slice<8>().val()), p_celloutsig__0__7z.slice<0>().val()))).val());
	// \src: ../top_100.sv:97.33-97.133
	// cell $xnor$../top_100.sv:97$37
	p_celloutsig__0__19z = xnor_uu<6>(p_celloutsig__0__13z.slice<6,3>().concat(p_celloutsig__0__16z).concat(p_celloutsig__0__0z).val(), p_in__data.slice<45,41>().concat(p_celloutsig__0__16z).val());
	// cells $eqx$../top_100.sv:80$20 $xor$../top_100.sv:63$10
	p_celloutsig__1__19z = eqx_uu<1>(p___01__.curr.slice<11,8>().val(), p_in__data.slice<168,166>().concat(xor_uu<1>(p_celloutsig__1__12z, p_celloutsig__1__4z)).val());
	// cells $procdff$48 $ne$../top_100.sv:83$23
	if (posedge_p_clkin__data_0) {
		p___02__.next = p___01__.curr.slice<6,3>().concat(ne_uu<1>(p_celloutsig__1__2z.slice<2,0>().concat(p_celloutsig__1__0z).val(), p_in__data.slice<174,171>().val())).val();
	}
	if (p_clkin__data.slice<64>().val() == value<1> {0u}) {
		p___02__.next = value<5>{0u};
	}
	// \always_ff: 1
	// \src: ../top_100.sv:69.7-71.54
	// cell $procdff$43
	if (negedge_p_celloutsig__1__19z) {
		p___11__.next = p_in__data.slice<48,43>().concat(p_celloutsig__0__0z).val();
	}
	if (p_clkin__data.slice<32>().val() == value<1> {1u}) {
		p___11__.next = value<7>{0u};
	}
	// \always_ff: 1
	// \src: ../top_100.sv:73.7-75.34
	// cell $procdff$40
	if (posedge_p_clkin__data_0) {
		p___01__.next = p_in__data.slice<107,96>().val();
	}
	if (p_clkin__data.slice<64>().val() == value<1> {1u}) {
		p___01__.next = value<12>{0u};
	}
	// connection
	p_inj__param__out__547 = p_celloutsig__0__8z;
	// cells $lt$../top_100.sv:81$21 $reduce_or$../top_100.sv:89$29 $reduce_or$../top_100.sv:92$32 $logic_not$../top_100.sv:59$2 $or$../top_100.sv:62$9 $not$../top_100.sv:62$8
	p_out__data.slice<128>().concat(p_out__data.slice<96>()).concat(p_out__data.slice<32>()).concat(p_out__data.slice<0>()) = or_uu<1>(p_celloutsig__1__12z, not_u<1>(p_celloutsig__1__0z)).concat(p_celloutsig__1__19z).concat(reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__2z).concat(p_celloutsig__0__19z.slice<1,0>()).concat(logic_not<1>(p_celloutsig__0__12z.slice<1>().val())).val())).concat(lt_uu<1>(p_celloutsig__0__19z.slice<5,3>().concat(p_celloutsig__0__16z).concat(reduce_or<1>(p_celloutsig__0__13z)).val(), p_celloutsig__0__8z.slice<4,0>().val())).val();
	return converged;
}

void p_topi::debug_eval() {
	// \src: ../top_100.sv:85.32-85.48
	// cell $reduce_or$../top_100.sv:85$25
	p_celloutsig__0__0z = reduce_or<1>(p_in__data.slice<84,76>().val());
	// cells $logic_not$../top_100.sv:60$4 $ternary$../top_100.sv:60$3
	p_celloutsig__0__2z = logic_not<1>((p_celloutsig__0__0z ? value<1>{0x1u} : p_in__data.slice<47>().val()));
	// \src: ../top_100.sv:91.32-91.94
	// cell $reduce_or$../top_100.sv:91$31
	p_celloutsig__0__3z = reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__2z).val());
	// \src: ../top_100.sv:79.32-79.254
	// cell $eqx$../top_100.sv:79$19
	p_celloutsig__0__4z = eqx_uu<1>(p_celloutsig__0__3z.concat(p_celloutsig__0__2z).concat(p_celloutsig__0__3z.repeat<2>()).concat(p_celloutsig__0__2z).concat(p_celloutsig__0__0z.repeat<2>()).concat(p_celloutsig__0__2z.repeat<2>()).val(), p_celloutsig__0__2z.concat(p___11__.curr).concat(p_celloutsig__0__0z).val());
	// \src: ../top_100.sv:64.32-64.59
	// cell $xor$../top_100.sv:64$11
	p_celloutsig__1__0z = xor_uu<1>(p_in__data.slice<144>().val(), p_in__data.slice<107>().val());
	// \src: ../top_100.sv:96.32-96.143
	// cell $xnor$../top_100.sv:96$36
	p_celloutsig__0__8z = xnor_uu<8>(p_celloutsig__0__4z.concat(p___11__.curr).val(), p___11__.curr.slice<5,0>().concat(p_celloutsig__0__3z.repeat<2>()).val());
	// \src: ../top_100.sv:84.32-84.145
	// cell $or$../top_100.sv:84$24
	p_celloutsig__0__7z = or_uu<9>(p_in__data.slice<82,74>().val(), p___11__.curr.slice<4,0>().concat(p_celloutsig__0__2z).concat(p_celloutsig__0__3z.repeat<2>()).concat(p_celloutsig__0__2z).val());
	// \src: ../top_100.sv:77.32-77.115
	// cell $div$../top_100.sv:77$17
	p_celloutsig__1__1z = div_uu<4>(p_in__data.slice<168,167>().concat(p_celloutsig__1__0z.repeat<2>()).val(), value<1>{0x1u}.concat(p_in__data.slice<126,124>()).val());
	// \src: ../top_100.sv:76.32-76.143
	// cell $div$../top_100.sv:76$16
	p_celloutsig__0__9z = div_uu<13>(p_in__data.slice<26,21>().concat(p___11__.curr).val(), value<1>{0x1u}.concat(p_celloutsig__0__7z.slice<5,3>()).concat(p_celloutsig__0__8z).concat(p_celloutsig__0__0z).val());
	// \src: ../top_100.sv:95.32-95.125
	// cell $sshl$../top_100.sv:95$35
	p_celloutsig__1__2z = sshl_uu<6>(p_celloutsig__1__1z.concat(p_celloutsig__1__0z.repeat<2>()).val(), p_in__data.slice<97,96>().concat(p_celloutsig__1__1z).val());
	// \src: ../top_100.sv:90.32-90.75
	// cell $reduce_or$../top_100.sv:90$30
	p_celloutsig__1__4z = reduce_or<1>(p_celloutsig__1__2z.slice<5,3>().concat(p_celloutsig__1__0z).val());
	// \src: ../top_100.sv:88.32-88.96
	// cell $reduce_or$../top_100.sv:88$28
	p_celloutsig__0__6z = reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__4z).concat(p_celloutsig__0__2z).val());
	// \src: ../top_100.sv:93.32-93.123
	// cell $sshl$../top_100.sv:93$33
	p_celloutsig__1__9z = sshl_uu<12>(p_celloutsig__1__4z.concat(p_celloutsig__1__1z).concat(p_celloutsig__1__2z).concat(p_celloutsig__1__0z).val(), p_in__data.slice<130,119>().val());
	// cells $sshl$../top_100.sv:94$34 $reduce_or$../top_100.sv:88$28
	p_celloutsig__0__12z = sshl_uu<3>(p_celloutsig__0__7z.slice<7,5>().concat(p_celloutsig__0__6z).val(), p_in__data.slice<81,78>().val());
	// cells $not$../top_100.sv:61$7 $and$../top_100.sv:61$6 $or$../top_100.sv:61$5 $div$../top_100.sv:76$16
	p_celloutsig__0__11z = not_u<1>(and_uu<1>(or_uu<1>(p_celloutsig__0__9z.slice<0>().val(), p_in__data.slice<8>().val()), p_celloutsig__0__7z.slice<0>().val()));
	// cells $reduce_or$../top_100.sv:87$27 $sshl$../top_100.sv:93$33
	p_celloutsig__1__12z = reduce_or<1>(p_celloutsig__1__9z.slice<11,8>().concat(p_celloutsig__1__2z.slice<5,3>()).concat(p_celloutsig__1__0z).concat(p___02__.curr).concat(p___01__.curr.slice<10,0>()).val());
	// \src: ../top_100.sv:82.33-82.99
	// cell $ne$../top_100.sv:82$22
	p_celloutsig__0__16z = ne_uu<1>(p_celloutsig__0__7z.slice<1,0>().concat(p_celloutsig__0__2z).val(), p_celloutsig__0__12z);
	// cells $div$../top_100.sv:78$18 $not$../top_100.sv:61$7 $and$../top_100.sv:61$6 $or$../top_100.sv:61$5 $div$../top_100.sv:76$16
	p_celloutsig__0__13z = div_uu<7>(p_in__data.slice<30,24>().val(), value<1>{0x1u}.concat(p_celloutsig__0__7z.slice<8,4>()).concat(p_celloutsig__0__11z).val());
	// \src: ../top_100.sv:63.33-63.67
	// cell $xor$../top_100.sv:63$10
	p_celloutsig__1__14z = xor_uu<1>(p_celloutsig__1__12z, p_celloutsig__1__4z);
	// \src: ../top_100.sv:97.33-97.133
	// cell $xnor$../top_100.sv:97$37
	p_celloutsig__0__19z = xnor_uu<6>(p_celloutsig__0__13z.slice<6,3>().concat(p_celloutsig__0__16z).concat(p_celloutsig__0__0z).val(), p_in__data.slice<45,41>().concat(p_celloutsig__0__16z).val());
	// \src: ../top_100.sv:59.33-59.95
	// cell $logic_not$../top_100.sv:59$2
	p_celloutsig__0__15z = logic_not<1>(p_celloutsig__0__12z.slice<1>().val());
	// \src: ../top_100.sv:89.33-89.51
	// cell $reduce_or$../top_100.sv:89$29
	p_celloutsig__0__17z = reduce_or<1>(p_celloutsig__0__13z);
	// \src: ../top_100.sv:83.32-83.93
	// cell $ne$../top_100.sv:83$23
	p_celloutsig__1__3z = ne_uu<1>(p_celloutsig__1__2z.slice<2,0>().concat(p_celloutsig__1__0z).val(), p_in__data.slice<174,171>().val());
	// cells $reduce_or$../top_100.sv:92$32 $logic_not$../top_100.sv:59$2
	p_celloutsig__0__25z = reduce_or<1>(p___11__.curr.concat(p_in__data.slice<15,3>()).concat(p_celloutsig__0__2z).concat(p_celloutsig__0__19z.slice<1,0>()).concat(p_celloutsig__0__15z).val());
	// cells $or$../top_100.sv:62$9 $not$../top_100.sv:62$8
	p_celloutsig__1__18z = or_uu<1>(p_celloutsig__1__12z, not_u<1>(p_celloutsig__1__0z));
	// cells $lt$../top_100.sv:81$21 $reduce_or$../top_100.sv:89$29
	p_celloutsig__0__26z = lt_uu<1>(p_celloutsig__0__19z.slice<5,3>().concat(p_celloutsig__0__16z).concat(p_celloutsig__0__17z).val(), p_celloutsig__0__8z.slice<4,0>().val());
}

CXXRTL_EXTREMELY_COLD
void p_topi::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "topi", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../top_100.sv:10.1-100.10" },
		}), std::move(cell_attrs));
		scopes->add(path, "module_with_params_inst_1000", "module_with_params", "src\000s../top_100.sv:1.1-8.10\000", "src\000s../top_100.sv:55.24-58.6\000");
	}
	if (items) {
		items->add(path, "module_with_params_inst_1000 param_out", "src\000s../top_100.sv:5.23-5.32\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "module_with_params_inst_1000 param_in", "src\000s../top_100.sv:4.22-4.30\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "_01_", "src\000s../top_100.sv:17.18-17.22\000", p___01__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "_02_", "src\000s../top_100.sv:18.17-18.21\000", p___02__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "_11_", "src\000s../top_100.sv:68.17-68.21\000", p___11__, 0, debug_item::DRIVEN_SYNC);
		items->add(path, "celloutsig_0_0z", "src\000s../top_100.sv:20.12-20.27\000", debug_eval_outline, p_celloutsig__0__0z);
		items->add(path, "celloutsig_0_11z", "src\000s../top_100.sv:21.12-21.28\000", debug_eval_outline, p_celloutsig__0__11z);
		items->add(path, "celloutsig_0_12z", "", debug_eval_outline, p_celloutsig__0__12z);
		items->add(path, "celloutsig_0_13z", "src\000s../top_100.sv:23.18-23.34\000", debug_eval_outline, p_celloutsig__0__13z);
		items->add(path, "celloutsig_0_15z", "src\000s../top_100.sv:24.12-24.28\000", debug_eval_outline, p_celloutsig__0__15z);
		items->add(path, "celloutsig_0_16z", "src\000s../top_100.sv:25.12-25.28\000", debug_eval_outline, p_celloutsig__0__16z);
		items->add(path, "celloutsig_0_17z", "src\000s../top_100.sv:26.12-26.28\000", debug_eval_outline, p_celloutsig__0__17z);
		items->add(path, "celloutsig_0_19z", "src\000s../top_100.sv:27.18-27.34\000unused_bits\000s2\000", debug_eval_outline, p_celloutsig__0__19z);
		items->add(path, "celloutsig_0_25z", "src\000s../top_100.sv:28.12-28.28\000", debug_eval_outline, p_celloutsig__0__25z);
		items->add(path, "celloutsig_0_26z", "src\000s../top_100.sv:29.12-29.28\000", debug_eval_outline, p_celloutsig__0__26z);
		items->add(path, "celloutsig_0_2z", "src\000s../top_100.sv:30.12-30.27\000", debug_eval_outline, p_celloutsig__0__2z);
		items->add(path, "celloutsig_0_3z", "src\000s../top_100.sv:31.12-31.27\000", debug_eval_outline, p_celloutsig__0__3z);
		items->add(path, "celloutsig_0_4z", "src\000s../top_100.sv:32.12-32.27\000", debug_eval_outline, p_celloutsig__0__4z);
		items->add(path, "celloutsig_0_6z", "src\000s../top_100.sv:33.12-33.27\000", debug_eval_outline, p_celloutsig__0__6z);
		items->add(path, "celloutsig_0_7z", "unused_bits\000s2\000", debug_eval_outline, p_celloutsig__0__7z);
		items->add(path, "celloutsig_0_8z", "src\000s../top_100.sv:35.18-35.33\000", debug_eval_outline, p_celloutsig__0__8z);
		items->add(path, "celloutsig_0_9z", "src\000s../top_100.sv:36.19-36.34\000unused_bits\000s1 2 3 4 5 6 7 8 9 10 11 12\000", debug_eval_outline, p_celloutsig__0__9z);
		items->add(path, "celloutsig_1_0z", "src\000s../top_100.sv:37.12-37.27\000", debug_eval_outline, p_celloutsig__1__0z);
		items->add(path, "celloutsig_1_12z", "src\000s../top_100.sv:39.12-39.28\000", debug_eval_outline, p_celloutsig__1__12z);
		items->add(path, "celloutsig_1_14z", "src\000s../top_100.sv:40.12-40.28\000", debug_eval_outline, p_celloutsig__1__14z);
		items->add(path, "celloutsig_1_18z", "src\000s../top_100.sv:41.12-41.28\000", debug_eval_outline, p_celloutsig__1__18z);
		items->add(path, "celloutsig_1_19z", "src\000s../top_100.sv:42.12-42.28\000", p_celloutsig__1__19z, 0, debug_item::DRIVEN_COMB);
		items->add(path, "celloutsig_1_1z", "src\000s../top_100.sv:43.18-43.33\000", debug_eval_outline, p_celloutsig__1__1z);
		items->add(path, "celloutsig_1_2z", "src\000s../top_100.sv:44.18-44.33\000", debug_eval_outline, p_celloutsig__1__2z);
		items->add(path, "celloutsig_1_3z", "src\000s../top_100.sv:45.12-45.27\000", debug_eval_outline, p_celloutsig__1__3z);
		items->add(path, "celloutsig_1_4z", "src\000s../top_100.sv:46.12-46.27\000", debug_eval_outline, p_celloutsig__1__4z);
		items->add(path, "celloutsig_1_9z", "src\000s../top_100.sv:47.19-47.34\000unused_bits\000s0 1 2 3 4 5 6 7\000", debug_eval_outline, p_celloutsig__1__9z);
		items->add(path, "clkin_data", "src\000s../top_100.sv:48.20-48.30\000", p_clkin__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "in_data", "src\000s../top_100.sv:50.21-50.28\000", p_in__data, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "inj_param_out_547", "src\000s../top_100.sv:54.23-54.40\000", p_inj__param__out__547, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "out_data", "src\000s../top_100.sv:52.22-52.30\000", p_out__data, 0, debug_item::OUTPUT|debug_item::UNDRIVEN|debug_item::DRIVEN_COMB);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_topi>(new cxxrtl_design::p_topi) };
}
