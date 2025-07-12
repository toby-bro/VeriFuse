package verilog

import (
	"testing"
)

func TestParseTypedefs(t *testing.T) {
	tests := []struct {
		input    string
		expected map[string]*Typedef // expected typedef names
	}{
		{
			"typedef class forward_my_class_t;",
			map[string]*Typedef{
				"forward_my_class_t": {
					Name:    "forward_my_class_t",
					Content: "typedef class forward_my_class_t;",
				},
			},
		},
		{
			"class forward_my_class_t;\n    int data;\n    function new(); data = 0; endfunction\nendclass",
			map[string]*Typedef{},
		},
		{
			"typedef struct { int data; } my_struct_t;",
			map[string]*Typedef{
				"my_struct_t": {
					Name:    "my_struct_t",
					Content: "typedef struct { int data; } my_struct_t;",
				},
			},
		},
		{
			"typedef struct packed {\n    logic [3:0] field_ps1;\n} my_packed_struct_t;",
			map[string]*Typedef{
				"my_packed_struct_t": {
					Name:    "my_packed_struct_t",
					Content: "typedef struct packed {\n    logic [3:0] field_ps1;\n} my_packed_struct_t;",
				},
			},
		},
		{
			"typedef int my_queue_t[$];",
			map[string]*Typedef{
				"my_queue_t": {Name: "my_queue_t", Content: "typedef int my_queue_t[$];"},
			},
		},
		{
			"typedef enum { ALIAS_A, ALIAS_B } my_enum_t;",
			map[string]*Typedef{
				"my_enum_t": {
					Name:    "my_enum_t",
					Content: "typedef enum { ALIAS_A, ALIAS_B } my_enum_t;",
				},
			},
		},
		{
			"typedef enum { E_A_alias, E_B_alias = 5, E_C_alias } simple_enum_t;",
			map[string]*Typedef{
				"simple_enum_t": {
					Name:    "simple_enum_t",
					Content: "typedef enum { E_A_alias, E_B_alias = 5, E_C_alias } simple_enum_t;",
				},
			},
		},
		{
			"typedef enum bit [2:0] { E_D=0, E_E=1, E_F=7 } base_type_enum_t;",
			map[string]*Typedef{
				"base_type_enum_t": {
					Name:    "base_type_enum_t",
					Content: "typedef enum bit [2:0] { E_D=0, E_E=1, E_F=7 } base_type_enum_t;",
				},
			},
		},
		{
			"typedef enum { E_G [0:3] } range_enum_t;",
			map[string]*Typedef{
				"range_enum_t": {
					Name:    "range_enum_t",
					Content: "typedef enum { E_G [0:3] } range_enum_t;",
				},
			},
		},
		{
			"typedef enum { D_H = 1, D_I = 2, D_J = 3 } duplicate_enum_t;",
			map[string]*Typedef{
				"duplicate_enum_t": {
					Name:    "duplicate_enum_t",
					Content: "typedef enum { D_H = 1, D_I = 2, D_J = 3 } duplicate_enum_t;",
				},
			},
		},
		{
			"typedef enum bit [1:0] { O_J=0, O_K=1, O_L=3 } overflow_enum_t;",
			map[string]*Typedef{
				"overflow_enum_t": {
					Name:    "overflow_enum_t",
					Content: "typedef enum bit [1:0] { O_J=0, O_K=1, O_L=3 } overflow_enum_t;",
				},
			},
		},
		{
			"typedef enum bit [1:0] { O_M=0, O_N=2 } overflow_enum_check_t;",
			map[string]*Typedef{
				"overflow_enum_check_t": {
					Name:    "overflow_enum_check_t",
					Content: "typedef enum bit [1:0] { O_M=0, O_N=2 } overflow_enum_check_t;",
				},
			},
		},
		{
			"typedef enum logic { U_M = 0, U_X = 1 } unknown_bits_default_t;",
			map[string]*Typedef{
				"unknown_bits_default_t": {
					Name:    "unknown_bits_default_t",
					Content: "typedef enum logic { U_M = 0, U_X = 1 } unknown_bits_default_t;",
				},
			},
		},
		{
			"typedef enum bit [0:0] { U_N = 0, U_Z = 1 } unknown_bits_2state_t;",
			map[string]*Typedef{
				"unknown_bits_2state_t": {
					Name:    "unknown_bits_2state_t",
					Content: "typedef enum bit [0:0] { U_N = 0, U_Z = 1 } unknown_bits_2state_t;",
				},
			},
		},
		{
			"typedef struct packed {\n    logic [3:0] field1;\n    logic [3:0] field2;\n} packed_struct_t;",
			map[string]*Typedef{
				"packed_struct_t": {
					Name:    "packed_struct_t",
					Content: "typedef struct packed {\n    logic [3:0] field1;\n    logic [3:0] field2;\n} packed_struct_t;",
				},
			},
		},
		{
			"typedef struct packed {\n    logic [3:0] field_ok;\n} packed_struct_good_member_t;",
			map[string]*Typedef{
				"packed_struct_good_member_t": {
					Name:    "packed_struct_good_member_t",
					Content: "typedef struct packed {\n    logic [3:0] field_ok;\n} packed_struct_good_member_t;",
				},
			},
		},
		{
			"typedef struct packed {\n    logic [3:0] field_a;\n    logic [3:0] field_b;\n} packed_struct_no_init_t;",
			map[string]*Typedef{
				"packed_struct_no_init_t": {
					Name:    "packed_struct_no_init_t",
					Content: "typedef struct packed {\n    logic [3:0] field_a;\n    logic [3:0] field_b;\n} packed_struct_no_init_t;",
				},
			},
		},
		{
			"typedef struct {\n    int field_int;\n    real field_real;\n    logic [7:0] field_vec;\n    rand int rand_field;\n    randc logic [3:0] randc_field;\n} unpacked_struct_t;",
			map[string]*Typedef{
				"unpacked_struct_t": {
					Name:    "unpacked_struct_t",
					Content: "typedef struct {\n    int field_int;\n    real field_real;\n    logic [7:0] field_vec;\n    rand int rand_field;\n    randc logic [3:0] randc_field;\n} unpacked_struct_t;",
				},
			},
		},
		{
			"typedef union packed {\n    logic [7:0] u_field1;\n    logic [7:0] u_field2;\n} packed_union_t;",
			map[string]*Typedef{
				"packed_union_t": {
					Name:    "packed_union_t",
					Content: "typedef union packed {\n    logic [7:0] u_field1;\n    logic [7:0] u_field2;\n} packed_union_t;",
				},
			},
		},
		{
			"typedef union {\n    int uv_field1;\n    real uv_field2;\n} unpacked_union_t;",
			map[string]*Typedef{
				"unpacked_union_t": {
					Name:    "unpacked_union_t",
					Content: "typedef union {\n    int uv_field1;\n    real uv_field2;\n} unpacked_union_t;",
				},
			},
		},
		{
			"typedef union {\n    int uv_field_int;\n    real uv_field_real;\n} unpacked_union_real_t;",
			map[string]*Typedef{
				"unpacked_union_real_t": {
					Name:    "unpacked_union_real_t",
					Content: "typedef union {\n    int uv_field_int;\n    real uv_field_real;\n} unpacked_union_real_t;",
				},
			},
		},
		{
			"typedef union tagged {\n    int tu_field_int;\n    real tu_field_real;\n} tagged_union_t;",
			map[string]*Typedef{
				"tagged_union_t": {
					Name:    "tagged_union_t",
					Content: "typedef union tagged {\n    int tu_field_int;\n    real tu_field_real;\n} tagged_union_t;",
				},
			},
		},
		{
			"typedef union {\n    int good_member;\n} unpacked_union_good_member_t;",
			map[string]*Typedef{
				"unpacked_union_good_member_t": {
					Name:    "unpacked_union_good_member_t",
					Content: "typedef union {\n    int good_member;\n} unpacked_union_good_member_t;",
				},
			},
		},
	}

	for _, tt := range tests {
		v := &VerilogFile{}
		err := v.parseTypedefs(tt.input)
		if err != nil {
			t.Errorf("parseTypedefs(%q) returned error: %v", tt.input, err)
			continue
		}
		if len(v.Typedefs) != len(tt.expected) {
			t.Errorf(
				"parseTypedefs(%q) typedef count = %d, want %d",
				tt.input,
				len(v.Typedefs),
				len(tt.expected),
			)
			continue
		}
		for name, expected := range tt.expected {
			if actual, ok := v.Typedefs[name]; !ok {
				t.Errorf("parseTypedefs(%q) missing typedef %q", tt.input, name)
			} else if actual.Content != expected.Content {
				t.Errorf("parseTypedefs(%q) typedef %q content = %q, want %q",
					tt.input, name, actual.Content, expected.Content)
			}
		}
	}
}

func TestPrintTypedef(t *testing.T) {
	tests := []struct {
		name string
		tdf  *Typedef
		want string
	}{
		{
			name: "SimpleTypedef",
			tdf: &Typedef{
				Name:    "my_typedef_t",
				Content: "typedef logic [7:0] my_typedef_t;",
			},
			want: "typedef logic [7:0] my_typedef_t;",
		},
		{
			name: "StructTypedef",
			tdf: &Typedef{
				Name:    "my_struct_t",
				Content: "typedef struct packed {\n    logic [0:0] field1;\n    logic [1:0] field2;\n} my_struct_t;",
			},
			want: "typedef struct packed {\n    logic [0:0] field1;\n    logic [1:0] field2;\n} my_struct_t;",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if printTypedef(tt.tdf) != tt.want {
				t.Errorf("printTypedef() = %v, want %v", printTypedef(tt.tdf), tt.want)
			}
		})
	}
}
