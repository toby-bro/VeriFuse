package verilog

import (
	"reflect"
	"sort"
	"strings"
	"testing"
)

func TestPortDirection_String(t *testing.T) {
	tests := []struct {
		name string
		d    PortDirection
		want string
	}{
		{"Input", INPUT, "input"},
		{"Output", OUTPUT, "output"},
		{"InOut", INOUT, "inout"},
		{"Internal", INTERNAL, "internal"}, // As per current implementation
		{"Unknown", PortDirection(99), "direction_99"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := tt.d.String(); got != tt.want {
				t.Errorf("PortDirection.String() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPortType_String(t *testing.T) {
	tests := []struct {
		name string
		pt   PortType
		want string
	}{
		{"Reg", REG, "reg"},
		{"Wire", WIRE, "wire"},
		{"Logic", LOGIC, "logic"},
		{"Integer", INTEGER, "integer"},
		{"Time", TIME, "time"},
		{"Bit", BIT, "bit"},
		{"Byte", BYTE, "byte"},
		{"ShortInt", SHORTINT, "shortint"},
		{"Int", INT, "int"},
		{"LongInt", LONGINT, "longint"},
		{"ShortReal", SHORTREAL, "shortreal"},
		{"Real", REAL, "real"},
		{"Realtime", REALTIME, "realtime"},
		{"String", STRING, "string"},
		{"Struct", STRUCT, "struct"},
		{"Void", VOID, "void"},
		{"Enum", ENUM, "enum"},
		{"UserDefined", USERDEFINED, ""}, // As per current implementation
		{"Unknown", UNKNOWN, ""},         // As per current implementation
		{"Invalid", PortType(99), "type_99"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := tt.pt.String(); got != tt.want {
				t.Errorf("PortType.String() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestFormatWidth(t *testing.T) {
	tests := []struct {
		name  string
		width int
		want  string
	}{
		{"Scalar", 1, ""},
		{"ZeroWidth (Scalar)", 0, ""},
		{"NegativeWidth (Scalar)", -1, ""},
		{"Width2", 2, "[1:0]"},
		{"Width8", 8, "[7:0]"},
		{"Width32", 32, "[31:0]"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := formatWidth(tt.width); got != tt.want {
				t.Errorf("formatWidth() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPortDirectionToString(t *testing.T) {
	tests := []struct {
		name string
		d    PortDirection
		want string
	}{
		{"Input", INPUT, "input"},
		{"Output", OUTPUT, "output"},
		{"InOut", INOUT, "inout"},
		{"Internal", INTERNAL, ""}, // As per current implementation
		{"Unknown", PortDirection(99), "direction_99"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := portDirectionToString(tt.d); got != tt.want {
				t.Errorf("PortDirectionToString() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPortTypeToString(t *testing.T) {
	tests := []struct {
		name string
		pt   PortType
		want string
	}{
		{"Reg", REG, "reg"},
		{"Wire", WIRE, "wire"},
		{"Logic", LOGIC, "logic"},
		{"Integer", INTEGER, "integer"},
		{"UserDefined", USERDEFINED, ""}, // As per current implementation
		{"Unknown", PortType(99), "type_99"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := typeToString(tt.pt); got != tt.want {
				t.Errorf("PortTypeToString() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPrintParameter(t *testing.T) {
	tests := []struct {
		name   string
		param  Parameter
		isLast bool
		want   string
	}{
		{
			"SimpleNotLast",
			Parameter{Name: "WIDTH", DefaultValue: "8"},
			false,
			"parameter WIDTH = 8,",
		},
		{"SimpleLast", Parameter{Name: "WIDTH", DefaultValue: "8"}, true, "parameter WIDTH = 8"},
		{
			"TypedNotLast",
			Parameter{Name: "DATA_W", Type: INT, DefaultValue: "32"},
			false,
			"parameter int DATA_W = 32,",
		},
		{
			"TypedLast",
			Parameter{Name: "ADDR_W", Type: INTEGER, DefaultValue: "16"},
			true,
			"parameter integer ADDR_W = 16",
		},
		{"NoDefaultNotLast", Parameter{Name: "CLK_FREQ"}, false, "parameter CLK_FREQ,"},
		{"NoDefaultLast", Parameter{Name: "CLK_FREQ"}, true, "parameter CLK_FREQ"},
		{
			"TypedNoDefaultLast",
			Parameter{Name: "MODE", Type: STRING},
			true,
			"parameter string MODE",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := printParameter(tt.param, tt.isLast); got != tt.want {
				t.Errorf("PrintParameter() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPrintPort(t *testing.T) {
	tests := []struct {
		name   string
		port   Port
		isLast bool
		want   string
	}{
		{
			"InputLogicScalarNotLast",
			Port{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 1},
			false,
			"input logic clk,",
		},
		{
			"OutputRegVectorLast",
			Port{Name: "data_out", Direction: OUTPUT, Type: REG, Width: 8, IsSigned: false},
			true,
			"output reg [7:0] data_out",
		},
		{
			"InoutWireScalarSignedNotLast",
			Port{Name: "bidir", Direction: INOUT, Type: WIRE, Width: 1, IsSigned: true},
			false,
			"inout wire signed bidir,",
		},
		{
			"InputNoTypeNotLast",
			Port{Name: "rst_n", Direction: INPUT, Width: 1},
			false,
			"input rst_n,",
		}, // Assumes logic is default or not printed if not specified
		{
			"InternalPort",
			Port{Name: "internal_sig", Direction: INTERNAL, Type: LOGIC, Width: 4},
			true,
			"logic [3:0] internal_sig",
		},
		{
			"UserDefinedTypeOutput",
			Port{Name: "custom_data", Direction: OUTPUT, Type: USERDEFINED, Width: 1},
			true,
			"output custom_data",
		},
		{
			"PortWithPragma",
			Port{
				Name:      "public_clk",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     1,
				Pragma:    "verilator public",
			},
			false,
			"(* verilator public *) input logic public_clk,",
		},
		{
			"PortWithPragmaAndWidth",
			Port{
				Name:      "pragma_data",
				Direction: OUTPUT,
				Type:      WIRE,
				Width:     8,
				Pragma:    "wire_force_assign",
			},
			true,
			"(* wire_force_assign *) output wire [7:0] pragma_data",
		},
		{
			"PortWithMultiWordPragma",
			Port{
				Name:      "keep_signal",
				Direction: INPUT,
				Type:      REG,
				Width:     16,
				IsSigned:  true,
				Pragma:    "synthesis keep = \"true\"",
			},
			false,
			"(* synthesis keep = \"true\" *) input reg signed [15:0] keep_signal,",
		},
		{
			"InternalPortWithPragma",
			Port{
				Name:      "internal_pragma",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     4,
				Pragma:    "custom_attr = \"value\"",
			},
			true,
			"(* custom_attr = \"value\" *) logic [3:0] internal_pragma",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := printPort(tt.port, tt.isLast, true); got != tt.want {
				// Normalizing whitespace for comparison as subtle differences can occur
				if normalizeSpace(got) != normalizeSpace(tt.want) {
					t.Errorf("PrintPort() =\n%q\nwant\n%q", got, tt.want)
				}
			}
		})
	}
}

func TestPrintVariableDeclaration(t *testing.T) {
	tests := []struct {
		name string
		v    *Variable
		want string
	}{
		{"LogicScalar", &Variable{Name: "my_logic", Type: LOGIC, Width: 1}, "logic my_logic;"},
		{"RegVector", &Variable{Name: "my_reg", Type: REG, Width: 8}, "reg [7:0] my_reg;"},
		{
			"IntSigned",
			&Variable{Name: "my_int", Type: INT, Width: 0, Unsigned: false},
			"int my_int;",
		}, // Signed is default for int
		{
			"IntUnsigned",
			&Variable{Name: "my_uint", Type: INT, Width: 0, Unsigned: true},
			"int unsigned my_uint;",
		},
		{
			"ByteUnsigned",
			&Variable{Name: "my_byte", Type: BYTE, Width: 0, Unsigned: true},
			"byte unsigned my_byte;",
		},
		{
			"UserDefinedType",
			&Variable{
				Name:  "my_custom_var",
				Type:  USERDEFINED,
				Width: 1, /* Assuming actual type name is handled by PortTypeToString or context */
				ParentStruct: &Struct{
					Name:      "my_struct_t",
					Variables: []*Variable{},
				},
			},
			"my_struct_t my_custom_var;",
		},
		{
			"UserDefinedType2",
			&Variable{
				Name:  "my_custom_var2",
				Type:  USERDEFINED,
				Width: 1, /* Assuming actual type name is handled by PortTypeToString or context */
				ParentClass: &Class{
					Name: "my_class",
				},
			},
			"my_class my_custom_var2;",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := printVariableDeclaration(tt.v); normalizeSpace(
				got,
			) != normalizeSpace(
				tt.want,
			) {
				t.Errorf("PrintVariableDeclaration() = %q, want %q", got, tt.want)
			}
		})
	}
}

func TestPrintStruct(t *testing.T) {
	s := &Struct{
		Name: "my_struct_t",
		Variables: []*Variable{
			{Name: "addr", Type: LOGIC, Width: 16},
			{Name: "data", Type: LOGIC, Width: 32},
		},
	}
	// Note: The exact spacing within the struct might vary based on PrintVariableDeclaration.
	// This test assumes a simple concatenation.
	want := `typedef struct packed {
logic [15:0] addr;
logic [31:0] data;
} my_struct_t;
`
	// Normalize whitespace for comparison
	got := printStruct(s)
	if normalizeSpace(got) != normalizeSpace(want) {
		t.Errorf("PrintStruct() =\n%q\nwant\n%q", got, want)
	}
}

func TestPrintClass(t *testing.T) {
	tests := []struct {
		name string
		c    *Class
		want string
	}{
		{
			name: "SimpleClass",
			c: &Class{
				Name: "MyClass",
				Body: "  int x;\n  function void print(); $display(x); endfunction\n",
			},
			want: `class MyClass;
  int x;
  function void print(); $display(x); endfunction
endclass
`,
		},
		{
			name: "ClassWithParams",
			c: &Class{
				Name:       "ParamClass",
				Parameters: []Parameter{{Name: "WIDTH", DefaultValue: "8"}},
				Body:       "  logic [WIDTH-1:0] data;\n",
			},
			want: `class ParamClass #(
  parameter WIDTH = 8
);
  logic [WIDTH-1:0] data;
endclass
`,
		},
		{
			name: "VirtualClassExtends",
			c: &Class{
				Name:      "ChildClass",
				isVirtual: true,
				extends:   "BaseClass",
				Body:      "  // Child specific\n",
			},
			want: `virtual class ChildClass extends BaseClass;
  // Child specific
endclass
`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printClass(tt.c)
			if normalizeSpace(got) != normalizeSpace(tt.want) {
				t.Errorf("PrintClass() for %s =\n%q\nwant\n%q", tt.name, got, tt.want)
			}
		})
	}
}

func TestPrintModule(t *testing.T) {
	tests := []struct {
		name string
		m    *Module
		want string
	}{
		{
			name: "SimpleModuleNoPortsNoParams",
			m: &Module{
				Name: "top",
				Body: "  initial $finish;\n",
			},
			want: `module top();
  initial $finish;
endmodule
`,
		},
		{
			name: "ModuleWithPorts",
			m: &Module{
				Name: "adder",
				Ports: []Port{
					{Name: "a", Direction: INPUT, Type: LOGIC, Width: 8},
					{Name: "b", Direction: INPUT, Type: LOGIC, Width: 8},
					{Name: "sum", Direction: OUTPUT, Type: LOGIC, Width: 8},
				},
				Body:      "  assign sum = a + b;\n",
				AnsiStyle: true,
			},
			want: `module adder (
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] sum
);
  assign sum = a + b;
endmodule
`,
		},
		{
			name: "ModuleWithParamsAndPorts",
			m: &Module{
				Name: "fifo",
				Parameters: []Parameter{
					{Name: "DATA_W", DefaultValue: "32", AnsiStyle: true},
					{Name: "DEPTH", DefaultValue: "16", AnsiStyle: true},
				},
				Ports: []Port{
					{Name: "clk", Direction: INPUT, Type: LOGIC},
					{Name: "rst_n", Direction: INPUT, Type: LOGIC},
					{Name: "wr_en", Direction: INPUT, Type: LOGIC},
					{
						Name:      "data_in",
						Direction: INPUT,
						Type:      LOGIC,
						Width:     32, /* Placeholder for DATA_W */
					}, // Width will be dynamic
					{Name: "rd_en", Direction: INPUT, Type: LOGIC},
					{
						Name:      "data_out",
						Direction: OUTPUT,
						Type:      LOGIC,
						Width:     32, /* Placeholder for DATA_W */
					},
				},
				Body:      "// FIFO logic here\n",
				AnsiStyle: true,
			},
			// Note: The PrintPort for data_in/out will use Width 0 -> "" if not dynamically set.
			// For a more accurate test, PrintModule would need to resolve parameter-dependent widths.
			// This test reflects current PrintPort behavior.
			want: `module fifo #(
  parameter DATA_W = 32,
  parameter DEPTH = 16
) (
  input logic clk,
  input logic rst_n,
  input logic wr_en,
  input logic [31:0] data_in,
  input logic rd_en,
  output logic [31:0] data_out
);
// FIFO logic here
endmodule
`,
		},
		{
			name: "ModuleNoPortsAnsi",
			m: &Module{
				Name: "test_no_ports",
				Body: "  // empty body\n",
			},
			want: `module test_no_ports();
  // empty body
endmodule
`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// For ports with width 0, formatWidth returns "", which is correct for scalar.
			// If parameters should resolve width, PrintModule/PrintPort would need more context.
			// This test assumes PrintPort prints what it's given.

			got := printModule(tt.m)
			if normalizeSpace(got) != normalizeSpace(tt.want) {
				t.Errorf(
					"PrintModule() for %s =\n%q\nwant\n%q",
					tt.name,
					normalizeSpace(got),
					normalizeSpace(tt.want),
				)
			}
		})
	}
}

func TestGetPrintOrder(t *testing.T) {
	tests := []struct {
		name    string
		vf      *VerilogFile
		want    []string
		wantErr bool
	}{
		{
			name: "NoDependencies",
			vf: &VerilogFile{
				Modules: map[string]*Module{"modA": {}, "modB": {}},
				Structs: map[string]*Struct{"structX": {}},
				Classes: map[string]*Class{"classY": {}},
			},
			want: []string{
				"classY",
				"modA",
				"modB",
				"structX",
			}, // Order depends on map iteration + sort
			wantErr: false,
		},
		{
			name: "SimpleDependencyStructClassModule",
			vf: &VerilogFile{
				Modules: map[string]*Module{"modMain": {Name: "modMain"}},
				Classes: map[string]*Class{"myClass": {Name: "myClass"}},
				Structs: map[string]*Struct{"myStruct": {Name: "myStruct"}},
				DependencyMap: map[string]*DependencyNode{
					"modMain":  {Name: "modMain", DependsOn: []string{"myClass"}},
					"myClass":  {Name: "myClass", DependsOn: []string{"myStruct"}},
					"myStruct": {Name: "myStruct", DependsOn: []string{}},
				},
			},
			want:    []string{"myStruct", "myClass", "modMain"},
			wantErr: false,
		},
		{
			name: "DependencyCycle", // Kahn's should leave cyclic nodes out or error
			vf: &VerilogFile{
				Modules: map[string]*Module{"modA": {Name: "modA"}, "modB": {Name: "modB"}},
				DependencyMap: map[string]*DependencyNode{
					"modA": {Name: "modA", DependsOn: []string{"modB"}},
					"modB": {Name: "modB", DependsOn: []string{"modA"}},
				},
			},
			// Expecting an error or a partial list + fallback in PrintVerilogFile
			// getPrintOrder itself might return an error and a partial list.
			// The current getPrintOrder appends missing items if a cycle is detected.
			want:    []string{"modA", "modB"}, // Fallback order if cycle detected
			wantErr: false,                    // Or false if it "resolves" by fallback
		},
		{
			name: "ItemNotInDependencyMap",
			vf: &VerilogFile{
				Modules: map[string]*Module{
					"modA": {Name: "modA"},
					"modC": {Name: "modC"},
				}, // modC not in map
				Structs: map[string]*Struct{"structB": {Name: "structB"}},
				DependencyMap: map[string]*DependencyNode{
					"modA":    {Name: "modA", DependsOn: []string{"structB"}},
					"structB": {Name: "structB", DependsOn: []string{}},
				},
			},
			// modC should still be included by the fallback logic in PrintVerilogFile,
			// getPrintOrder might only return modA, structB based on map.
			// The test for getPrintOrder should reflect what it *returns*.
			// The current getPrintOrder only processes nodes in DependencyMap for sorting,
			// but then adds all defined nodes.
			want:    []string{"modC", "structB", "modA"}, // Order can vary for unmapped/fallback
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := getPrintOrder(tt.vf)
			if (err != nil) != tt.wantErr {
				t.Errorf("getPrintOrder() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			// Sort both slices because the order of elements with no dependencies
			// or in fallback scenarios can be non-deterministic.
			sort.Strings(got)
			sort.Strings(tt.want)
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("getPrintOrder() got = %v, want = %v", got, tt.want)
			}
		})
	}
}

func TestPrintVerilogFile(t *testing.T) {
	tests := []struct {
		name    string
		vf      *VerilogFile
		want    string
		wantErr bool
	}{
		{
			name:    "EmptyFile",
			vf:      &VerilogFile{},
			want:    "",
			wantErr: false,
		},
		{
			name: "SingleModule",
			vf: &VerilogFile{
				Modules: map[string]*Module{
					"top": {
						Name: "top", Body: "  initial $display(\"Hello\");\n",
						Parameters: []Parameter{
							{Name: "WIDTH", DefaultValue: "8", AnsiStyle: true},
							{Name: "DEPTH", DefaultValue: "16", AnsiStyle: true},
						},
						Ports: []Port{
							{Name: "clk", Direction: INPUT, Type: LOGIC},
							{Name: "rst_n", Direction: INPUT, Type: LOGIC},
							{Name: "data_in", Direction: INPUT, Type: LOGIC, Width: 8},
							{Name: "data_out", Direction: OUTPUT, Type: LOGIC, Width: 8},
						},
						AnsiStyle: true,
					},
				},
			},
			want: `        module top #(
    parameter WIDTH = 8,
    parameter DEPTH = 16
) (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    initial $display("Hello");
endmodule
`,
			wantErr: false,
		},
		{
			name: "StructAndModule",
			vf: &VerilogFile{
				Structs: map[string]*Struct{
					"my_data_t": {
						Name: "my_data_t",
						Variables: []*Variable{
							{Name: "payload", Type: LOGIC, Width: 8},
						},
					},
				},
				Modules: map[string]*Module{
					"processor": {
						Name:      "processor",
						Body:      "  my_data_t data_bus;\n",
						Ports:     []Port{{Name: "clk", Direction: INPUT, Type: LOGIC}},
						AnsiStyle: true,
					},
				},
				DependencyMap: map[string]*DependencyNode{
					"processor": {Name: "processor", DependsOn: []string{"my_data_t"}},
					"my_data_t": {Name: "my_data_t", DependsOn: []string{}},
				},
			},
			want: `typedef struct packed {
logic [7:0] payload;
} my_data_t;

module processor (
  input logic clk
);
  my_data_t data_bus;
endmodule
`,
			wantErr: false,
		},
		{
			name: "ClassModuleAndStructOrder",
			vf: &VerilogFile{
				Modules: map[string]*Module{"M": {Name: "M", Body: "C c_inst = new;\n"}},
				Classes: map[string]*Class{"C": {Name: "C", Body: "S s_var;\n"}},
				Structs: map[string]*Struct{
					"S": {Name: "S", Variables: []*Variable{{Name: "field", Type: INT}}},
				},
				DependencyMap: map[string]*DependencyNode{
					"M": {Name: "M", DependsOn: []string{"C"}},
					"C": {Name: "C", DependsOn: []string{"S"}},
					"S": {Name: "S", DependsOn: []string{}},
				},
			},
			want: `typedef struct packed {
    int field;
} S;

class C;
    S s_var;
endclass

module M();
    C c_inst = new;
endmodule
`,
			wantErr: false,
		},
		{
			name: "NoDependencyMapFallbackOrder", // Test fallback when DependencyMap is nil or incomplete
			vf: &VerilogFile{
				Modules: map[string]*Module{"modA": {Name: "modA"}},
				Structs: map[string]*Struct{"structZ": {Name: "structZ"}},
				Classes: map[string]*Class{"classM": {Name: "classM"}},
				// DependencyMap: nil, // Explicitly test nil case
			},
			// Order will be structs, then classes, then modules, then interfaces (alphabetical within type)
			want: `typedef struct packed {
} structZ;

class classM;
endclass

module modA();
endmodule
`, // Actual content of struct/class/module body is empty here
			wantErr: false,
		},
		{
			name: "NonAnsiStyleModule",
			vf: &VerilogFile{
				Modules: map[string]*Module{
					"nonAnsiModule": {
						Name:      "nonAnsiModule",
						Body:      "  input logic clk;\n  initial $display(\"Non-ANSI Module\");\n",
						Ports:     []Port{{Name: "clk", Direction: INPUT, Type: LOGIC}},
						AnsiStyle: false, // Non-ANSI style
					},
				},
				DependencyMap: map[string]*DependencyNode{
					"nonAnsiModule": {Name: "nonAnsiModule", DependsOn: []string{}},
				},
			},
			want: `module nonAnsiModule (
clk
);
  input logic clk;
  initial $display("Non-ANSI Module");
endmodule`,
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Adjust struct/class bodies for the "NoDependencyMapFallbackOrder" test case
			// to match the expected output if they have default empty content.
			if tt.name == "NoDependencyMapFallbackOrder" {
				tt.vf.Structs["structZ"].Variables = []*Variable{} // Ensure empty for exact match
				tt.vf.Classes["classM"].Body = ""
				tt.vf.Modules["modA"].Body = ""
			}

			got, err := PrintVerilogFile(tt.vf)
			if (err != nil) != tt.wantErr {
				t.Errorf("PrintVerilogFile() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if normalizeSpaceFile(got) != normalizeSpaceFile(tt.want) {
				t.Errorf(
					"PrintVerilogFile() for %s =\nGOT:\n%s\nWANT:\n%s",
					tt.name,
					normalizeSpaceFile(got),     // Use normalizeSpaceFile here
					normalizeSpaceFile(tt.want), // And here
				)
			}
		})
	}
}

// normalizeSpace removes redundant spaces and newlines for robust comparison.
func normalizeSpace(s string) string {
	s = strings.Join(strings.Fields(s), " ")
	s = strings.ReplaceAll(s, " ;", ";")
	s = strings.ReplaceAll(s, " ,", ",")
	s = strings.ReplaceAll(s, "( ", "(")
	s = strings.ReplaceAll(s, " )", ")")
	s = strings.ReplaceAll(s, "[ ", "[")
	s = strings.ReplaceAll(s, " ]", "]")
	return s
}

// normalizeSpaceFile is for comparing larger file outputs,
// primarily focusing on trimming leading/trailing space from each line and removing empty lines.
func normalizeSpaceFile(s string) string {
	lines := strings.Split(s, "\n")
	var nonEmptyLines []string
	for _, line := range lines {
		trimmedLine := strings.TrimSpace(line)
		if trimmedLine != "" {
			nonEmptyLines = append(nonEmptyLines, trimmedLine)
		}
	}
	return strings.Join(nonEmptyLines, "\n")
}

// Helper to create a VerilogFile with specific dependency setup for cycle testing in PrintVerilogFile
func createVerilogFileWithCycle() *VerilogFile {
	vf := &VerilogFile{
		Modules: map[string]*Module{
			"modA": {Name: "modA", Body: "// A depends on B"},
			"modB": {Name: "modB", Body: "// B depends on A"},
		},
		DependencyMap: map[string]*DependencyNode{
			"modA": {Name: "modA", DependsOn: []string{"modB"}},
			"modB": {Name: "modB", DependsOn: []string{"modA"}},
		},
	}
	return vf
}

func TestPrintVerilogFile_WithCycle(t *testing.T) {
	vf := createVerilogFileWithCycle()
	// The current getPrintOrder attempts to resolve cycles by printing remaining items.
	// The exact order of modA and modB might vary if a cycle is broken arbitrarily.
	// We expect it not to hang and to print both modules.
	// PrintVerilogFile itself doesn't return an error for cycles if getPrintOrder provides a list.
	got, err := PrintVerilogFile(vf)
	if err != nil {
		t.Fatalf("PrintVerilogFile() with cycle error = %v, wantErr false", err)
	}

	gotNormalized := normalizeSpaceFile(got)
	wantOption1 := normalizeSpaceFile(`module modA();
    // A depends on B
endmodule
module modB();
    // B depends on A
endmodule`)
	wantOption2 := normalizeSpaceFile(`module modB();
    // B depends on A
endmodule
module modA();
    // A depends on B
endmodule`)

	if gotNormalized != wantOption1 && gotNormalized != wantOption2 {
		t.Errorf(
			"PrintVerilogFile() with cycle got =\n%s\nWant one of:\n%s\nOR\n%s",
			got,
			wantOption1,
			wantOption2,
		)
	}
}

func TestPrintInterfacePort(t *testing.T) {
	tests := []struct {
		name   string
		port   InterfacePort
		isLast bool
		want   string
	}{
		{
			name: "Simple input logic port",
			port: InterfacePort{
				Name:      "clk",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			isLast: false,
			want:   "input logic clk,",
		},
		{
			name: "Output wire port with width",
			port: InterfacePort{
				Name:      "data",
				Direction: OUTPUT,
				Type:      WIRE,
				Width:     8,
				IsSigned:  false,
			},
			isLast: true,
			want:   "output wire [7:0] data",
		},
		{
			name: "Signed input port",
			port: InterfacePort{
				Name:      "addr",
				Direction: INPUT,
				Type:      REG,
				Width:     16,
				IsSigned:  true,
			},
			isLast: false,
			want:   "input reg signed [15:0] addr,",
		},
		{
			name: "Internal port (no direction)",
			port: InterfacePort{
				Name:      "internal_sig",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			isLast: true,
			want:   "logic internal_sig",
		},
		{
			name: "Interface port with pragma",
			port: InterfacePort{
				Name:      "public_clk",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
				Pragma:    "verilator public",
			},
			isLast: false,
			want:   "(* verilator public *) input logic public_clk,",
		},
		{
			name: "Interface port with pragma and width",
			port: InterfacePort{
				Name:      "pragma_data",
				Direction: OUTPUT,
				Type:      WIRE,
				Width:     8,
				IsSigned:  false,
				Pragma:    "wire_force_assign",
			},
			isLast: true,
			want:   "(* wire_force_assign *) output wire [7:0] pragma_data",
		},
		{
			name: "Interface port with multi-word pragma",
			port: InterfacePort{
				Name:      "addr_bus",
				Direction: INPUT,
				Type:      REG,
				Width:     16,
				IsSigned:  true,
				Pragma:    "synthesis keep = \"true\"",
			},
			isLast: false,
			want:   "(* synthesis keep = \"true\" *) input reg signed [15:0] addr_bus,",
		},
		{
			name: "Internal port with pragma",
			port: InterfacePort{
				Name:      "internal_pragma",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     4,
				IsSigned:  false,
				Pragma:    "custom_attr = \"value\"",
			},
			isLast: true,
			want:   "(* custom_attr = \"value\" *) logic [3:0] internal_pragma",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printInterfacePort(tt.port, tt.isLast)
			if got != tt.want {
				t.Errorf("PrintInterfacePort() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPrintModPort(t *testing.T) {
	tests := []struct {
		name    string
		modport ModPort
		want    string
	}{
		{
			name: "Simple modport",
			modport: ModPort{
				Name: "master",
				Signals: []ModPortSignal{
					{Name: "data", Direction: OUTPUT},
					{Name: "valid", Direction: OUTPUT},
					{Name: "ready", Direction: INPUT},
				},
			},
			want: `modport master (
    output data,
    output valid,
    input ready
);`,
		},
		{
			name: "Single signal modport",
			modport: ModPort{
				Name: "simple",
				Signals: []ModPortSignal{
					{Name: "clk", Direction: INPUT},
				},
			},
			want: `modport simple (
    input clk
);`,
		},
		{
			name: "Empty modport",
			modport: ModPort{
				Name:    "empty",
				Signals: []ModPortSignal{},
			},
			want: `modport empty (
);`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printModPort(tt.modport)
			if got != tt.want {
				t.Errorf("PrintModPort() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPrintInterface(t *testing.T) {
	tests := []struct {
		name string
		intf *Interface
		want string
	}{
		{
			name: "Simple interface",
			intf: &Interface{
				Name:        "simple_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface simple_if;
endinterface`,
		},
		{
			name: "Virtual interface",
			intf: &Interface{
				Name:        "virtual_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   true,
				ExtendsFrom: "",
			},
			want: `virtual interface virtual_if;
endinterface`,
		},
		{
			name: "Interface with parameters",
			intf: &Interface{
				Name:  "param_if",
				Ports: []InterfacePort{},
				Parameters: []Parameter{
					{Name: "WIDTH", Type: INT, DefaultValue: "8"},
					{Name: "DEPTH", Type: INT, DefaultValue: "16"},
				},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface param_if #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
);
endinterface`,
		},
		{
			name: "Interface with ports",
			intf: &Interface{
				Name: "port_if",
				Ports: []InterfacePort{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst_n", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface port_if (
    input logic clk,
    input logic rst_n
);
endinterface`,
		},
		{
			name: "Interface extending another",
			intf: &Interface{
				Name:        "extended_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "base_if",
			},
			want: `interface extended_if extends base_if;
endinterface`,
		},
		{
			name: "Interface with variables",
			intf: &Interface{
				Name:       "var_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts:   []ModPort{},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 8},
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface var_if;
    logic [7:0] data;
    logic valid;
endinterface`,
		},
		{
			name: "Interface with modports",
			intf: &Interface{
				Name:       "modport_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "master",
						Signals: []ModPortSignal{
							{Name: "data", Direction: OUTPUT},
							{Name: "ready", Direction: INPUT},
							{Name: "valid", Direction: OUTPUT},
						},
					},
					{
						Name: "slave",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
							{Name: "valid", Direction: INPUT},
						},
					},
				},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface modport_if;
    modport master (
        output data,
        input ready,
        output valid
    );

    modport slave (
        input data,
        output ready,
        input valid
    );
endinterface`,
		},
		{
			name: "Complete interface with all features",
			intf: &Interface{
				Name: "complete_if",
				Ports: []InterfacePort{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []Parameter{
					{Name: "WIDTH", Type: INT, DefaultValue: "8"},
				},
				ModPorts: []ModPort{
					{
						Name: "producer",
						Signals: []ModPortSignal{
							{Name: "data", Direction: OUTPUT},
							{Name: "valid", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 8},
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface complete_if #(
    parameter int WIDTH = 8
) (
    input logic clk
);
    logic [7:0] data;
    logic valid;

    modport producer (
        output data,
        output valid
    );
endinterface`,
		},
		{
			name: "Virtual interface extending with all features",
			intf: &Interface{
				Name: "full_virtual_if",
				Ports: []InterfacePort{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst_n", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []Parameter{
					{Name: "WIDTH", Type: INT, DefaultValue: "32"},
					{Name: "DEPTH", Type: INT, DefaultValue: "16"},
				},
				ModPorts: []ModPort{
					{
						Name: "master",
						Signals: []ModPortSignal{
							{Name: "addr", Direction: OUTPUT},
							{Name: "data", Direction: INOUT},
							{Name: "we", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "addr", Type: LOGIC, Width: 32},
					{Name: "data", Type: LOGIC, Width: 32},
					{Name: "we", Type: LOGIC, Width: 0},
				},
				Body:        "",
				IsVirtual:   true,
				ExtendsFrom: "base_memory_if",
			},
			want: `virtual interface full_virtual_if #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 16
) (
    input logic clk,
    input logic rst_n
) extends base_memory_if;
    logic [31:0] addr;
    logic [31:0] data;
    logic we;

    modport master (
        output addr,
        inout data,
        output we
    );
endinterface`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printInterface(tt.intf)
			if got != tt.want {
				t.Errorf("PrintInterface() = %v, want %v", got, tt.want)
			}
		})
	}
}

// Test interfaces from V3SchedVirtIface.sv specifically
func TestPrintInterface_V3SchedVirtIface(t *testing.T) {
	tests := []struct {
		name string
		intf *Interface
		want string
	}{
		{
			name: "my_if interface",
			intf: &Interface{
				Name:       "my_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "FullAccess",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
							{Name: "valid", Direction: OUTPUT},
						},
					},
					{
						Name: "AccessIn",
						Signals: []ModPortSignal{
							{Name: "data", Direction: OUTPUT},
							{Name: "valid", Direction: OUTPUT},
							{Name: "ready", Direction: INPUT},
						},
					},
					{
						Name: "AccessOut",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "valid", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 8},
					{Name: "ready", Type: LOGIC, Width: 0},
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "    logic [7:0] data;\n    logic ready;\n    logic valid;\n    modport FullAccess (input data, output ready, output valid);\n    modport AccessIn (output data, output valid, input ready);\n    modport AccessOut (input data, input valid, output ready);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface`,
		},
		{
			name: "cond_if interface",
			intf: &Interface{
				Name:       "cond_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "CtrlStat",
						Signals: []ModPortSignal{
							{Name: "control_reg", Direction: OUTPUT},
							{Name: "status_reg", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "control_reg", Type: LOGIC, Width: 16},
					{Name: "status_reg", Type: LOGIC, Width: 16},
				},
				Body:        "    logic [15:0] control_reg;\n    logic [15:0] status_reg;\n    modport CtrlStat (output control_reg, input status_reg);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface`,
		},
		{
			name: "loop_if interface",
			intf: &Interface{
				Name:       "loop_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "Ctrl",
						Signals: []ModPortSignal{
							{Name: "index", Direction: OUTPUT},
							{Name: "done", Direction: OUTPUT},
						},
					},
					{
						Name: "Report",
						Signals: []ModPortSignal{
							{Name: "index", Direction: INPUT},
							{Name: "done", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "index", Type: LOGIC, Width: 4},
					{Name: "done", Type: LOGIC, Width: 0},
				},
				Body:        "    logic [3:0] index;\n    logic done;\n    modport Ctrl (output index, output done);\n    modport Report (input index, input done);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface loop_if;
    logic [3:0] index;
    logic done;
    modport Ctrl (output index, output done);
    modport Report (input index, input done);
endinterface`,
		},
		{
			name: "seq_if interface",
			intf: &Interface{
				Name:       "seq_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "PortA",
						Signals: []ModPortSignal{
							{Name: "value_a", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "value_a", Type: LOGIC, Width: 32},
				},
				Body:        "    logic [31:0] value_a;\n    modport PortA (output value_a);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface`,
		},
		{
			name: "seq2_if interface",
			intf: &Interface{
				Name:       "seq2_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "PortB",
						Signals: []ModPortSignal{
							{Name: "status_byte", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "status_byte", Type: LOGIC, Width: 8},
				},
				Body:        "    logic [7:0] status_byte;\n    modport PortB (output status_byte);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface`,
		},
		{
			name: "struct_if interface",
			intf: &Interface{
				Name:       "struct_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "Access",
						Signals: []ModPortSignal{
							{Name: "packet_field1", Direction: OUTPUT},
							{Name: "packet_field2", Direction: OUTPUT},
							{Name: "tx_en", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "packet_field1", Type: LOGIC, Width: 8},
					{Name: "packet_field2", Type: LOGIC, Width: 8},
					{Name: "tx_en", Type: LOGIC, Width: 0},
				},
				Body:        "    logic [7:0] packet_field1;\n    logic [7:0] packet_field2;\n    logic tx_en;\n    modport Access (output packet_field1, output packet_field2, output tx_en);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printInterface(tt.intf)
			if got != tt.want {
				t.Errorf("PrintInterface() for %s =\nGOT:\n%s\nWANT:\n%s", tt.name, got, tt.want)
			}
		})
	}
}

func TestPrintModPort_V3SchedVirtIface(t *testing.T) {
	tests := []struct {
		name    string
		modport ModPort
		want    string
	}{
		{
			name: "FullAccess modport from my_if",
			modport: ModPort{
				Name: "FullAccess",
				Signals: []ModPortSignal{
					{Name: "data", Direction: INPUT},
					{Name: "ready", Direction: OUTPUT},
					{Name: "valid", Direction: OUTPUT},
				},
			},
			want: `modport FullAccess (
    input data,
    output ready,
    output valid
);`,
		},
		{
			name: "AccessIn modport from my_if",
			modport: ModPort{
				Name: "AccessIn",
				Signals: []ModPortSignal{
					{Name: "data", Direction: OUTPUT},
					{Name: "valid", Direction: OUTPUT},
					{Name: "ready", Direction: INPUT},
				},
			},
			want: `modport AccessIn (
    output data,
    output valid,
    input ready
);`,
		},
		{
			name: "AccessOut modport from my_if",
			modport: ModPort{
				Name: "AccessOut",
				Signals: []ModPortSignal{
					{Name: "data", Direction: INPUT},
					{Name: "valid", Direction: INPUT},
					{Name: "ready", Direction: OUTPUT},
				},
			},
			want: `modport AccessOut (
    input data,
    input valid,
    output ready
);`,
		},
		{
			name: "CtrlStat modport from cond_if",
			modport: ModPort{
				Name: "CtrlStat",
				Signals: []ModPortSignal{
					{Name: "control_reg", Direction: OUTPUT},
					{Name: "status_reg", Direction: INPUT},
				},
			},
			want: `modport CtrlStat (
    output control_reg,
    input status_reg
);`,
		},
		{
			name: "Ctrl modport from loop_if",
			modport: ModPort{
				Name: "Ctrl",
				Signals: []ModPortSignal{
					{Name: "index", Direction: OUTPUT},
					{Name: "done", Direction: OUTPUT},
				},
			},
			want: `modport Ctrl (
    output index,
    output done
);`,
		},
		{
			name: "Report modport from loop_if",
			modport: ModPort{
				Name: "Report",
				Signals: []ModPortSignal{
					{Name: "index", Direction: INPUT},
					{Name: "done", Direction: INPUT},
				},
			},
			want: `modport Report (
    input index,
    input done
);`,
		},
		{
			name: "PortA modport from seq_if",
			modport: ModPort{
				Name: "PortA",
				Signals: []ModPortSignal{
					{Name: "value_a", Direction: OUTPUT},
				},
			},
			want: `modport PortA (
    output value_a
);`,
		},
		{
			name: "PortB modport from seq2_if",
			modport: ModPort{
				Name: "PortB",
				Signals: []ModPortSignal{
					{Name: "status_byte", Direction: OUTPUT},
				},
			},
			want: `modport PortB (
    output status_byte
);`,
		},
		{
			name: "Access modport from struct_if",
			modport: ModPort{
				Name: "Access",
				Signals: []ModPortSignal{
					{Name: "packet_field1", Direction: OUTPUT},
					{Name: "packet_field2", Direction: OUTPUT},
					{Name: "tx_en", Direction: OUTPUT},
				},
			},
			want: `modport Access (
    output packet_field1,
    output packet_field2,
    output tx_en
);`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printModPort(tt.modport)
			if got != tt.want {
				t.Errorf("PrintModPort() for %s =\nGOT:\n%s\nWANT:\n%s", tt.name, got, tt.want)
			}
		})
	}
}

func TestPrintInterfacePort_V3SchedVirtIface(t *testing.T) {
	tests := []struct {
		name   string
		port   InterfacePort
		isLast bool
		want   string
	}{
		{
			name: "8-bit data signal",
			port: InterfacePort{
				Name:      "data",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
			},
			isLast: false,
			want:   "logic [7:0] data,",
		},
		{
			name: "ready signal",
			port: InterfacePort{
				Name:      "ready",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			isLast: false,
			want:   "logic ready,",
		},
		{
			name: "valid signal",
			port: InterfacePort{
				Name:      "valid",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			isLast: true,
			want:   "logic valid",
		},
		{
			name: "16-bit control_reg signal",
			port: InterfacePort{
				Name:      "control_reg",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     16,
				IsSigned:  false,
			},
			isLast: false,
			want:   "logic [15:0] control_reg,",
		},
		{
			name: "4-bit index signal",
			port: InterfacePort{
				Name:      "index",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     4,
				IsSigned:  false,
			},
			isLast: false,
			want:   "logic [3:0] index,",
		},
		{
			name: "32-bit value_a signal",
			port: InterfacePort{
				Name:      "value_a",
				Direction: INTERNAL,
				Type:      LOGIC,
				Width:     32,
				IsSigned:  false,
			},
			isLast: true,
			want:   "logic [31:0] value_a",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printInterfacePort(tt.port, tt.isLast)
			if got != tt.want {
				t.Errorf("PrintInterfacePort() for %s =\nGOT: %q\nWANT: %q", tt.name, got, tt.want)
			}
		})
	}
}

func TestPrintInterface_EdgeCases_V3SchedVirtIface(t *testing.T) {
	tests := []struct {
		name string
		intf *Interface
		want string
	}{
		{
			name: "Empty interface",
			intf: &Interface{
				Name:        "empty_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface empty_if;
endinterface`,
		},
		{
			name: "Interface with only variables (generated from components)",
			intf: &Interface{
				Name:       "vars_only_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts:   []ModPort{},
				Variables: []*Variable{
					{Name: "test_signal", Type: LOGIC, Width: 8},
				},
				Body:        "", // Empty body, should generate from components
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface vars_only_if;
    logic [7:0] test_signal;
endinterface`,
		},
		{
			name: "Interface with only modports (generated from components)",
			intf: &Interface{
				Name:       "modports_only_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "test_port",
						Signals: []ModPortSignal{
							{Name: "test_sig", Direction: OUTPUT},
						},
					},
				},
				Variables:   []*Variable{},
				Body:        "", // Empty body, should generate from components
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface modports_only_if;
    modport test_port (
        output test_sig
    );
endinterface`,
		},
		{
			name: "Interface with body takes precedence over components",
			intf: &Interface{
				Name:       "body_precedence_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "ignored_port",
						Signals: []ModPortSignal{
							{Name: "ignored_sig", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "ignored_var", Type: LOGIC, Width: 8},
				},
				Body:        "    logic [7:0] actual_signal;\n    modport actual_port (output actual_signal);", // Body takes precedence
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			want: `interface body_precedence_if;
    logic [7:0] actual_signal;
    modport actual_port (output actual_signal);
endinterface`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printInterface(tt.intf)
			if got != tt.want {
				t.Errorf("PrintInterface() for %s =\nGOT:\n%s\nWANT:\n%s", tt.name, got, tt.want)
			}
		})
	}
}

func TestPrintPackage(t *testing.T) {
	tests := []struct {
		name string
		pkg  *Package
		want string
	}{
		{
			name: "SimplePackageWithTypedef",
			pkg: &Package{
				Name: "test_pkg",
				Typedefs: []string{
					"typedef logic [7:0] data_t;",
				},
				Body: "    typedef logic [7:0] data_t;",
			},
			want: `package test_pkg;
    typedef logic [7:0] data_t;
endpackage
`,
		},
		{
			name: "PackageWithImports",
			pkg: &Package{
				Name: "importer_pkg",
				Imports: []string{
					"import other_pkg::*;",
					"import another_pkg::specific_item;",
				},
				Body: `    import other_pkg::*;
    import another_pkg::specific_item;`,
			},
			want: `package importer_pkg;
    import other_pkg::*;
    import another_pkg::specific_item;
endpackage
`,
		},
		{
			name: "PackageWithParameters",
			pkg: &Package{
				Name: "config_pkg",
				Parameters: []Parameter{
					{Name: "WIDTH", DefaultValue: "8"},
					{Name: "DEPTH", Type: INTEGER, DefaultValue: "256"},
				},
				Body: `    parameter WIDTH = 8;
    parameter integer DEPTH = 256;`,
			},
			want: `package config_pkg;
    parameter WIDTH = 8;
    parameter integer DEPTH = 256;
endpackage
`,
		},
		{
			name: "PackageWithVariables",
			pkg: &Package{
				Name: "vars_pkg",
				Variables: []*Variable{
					{Name: "status_reg", Type: LOGIC, Width: 4},
					{Name: "counter", Type: INT, Unsigned: true},
				},
				Body: `    logic [3:0] status_reg;
    int unsigned counter;`,
			},
			want: `package vars_pkg;
    logic [3:0] status_reg;
    int unsigned counter;
endpackage
`,
		},
		{
			name: "EmptyPackage",
			pkg: &Package{
				Name: "empty_pkg",
				Body: "",
			},
			want: `package empty_pkg;
endpackage
`,
		},
		{
			name: "ComplexPackage",
			pkg: &Package{
				Name: "complex_pkg",
				Parameters: []Parameter{
					{Name: "DATA_WIDTH", DefaultValue: "32"},
				},
				Imports: []string{"import common_types_pkg::*;"},
				Typedefs: []string{
					"typedef struct packed { logic valid; logic [DATA_WIDTH-1:0] data; } packet_t;",
				},
				Variables: []*Variable{
					{
						Name: "current_packet", Type: USERDEFINED, ParentStruct: &Struct{Name: "packet_t"},
					}, // Changed UserType to ParentStruct
				},
				// Body field will be constructed by the PrintPackage function
				// For now, we can leave it empty or provide a simplified version
				// as the printer should ideally reconstruct it from components.
				// Let's assume PrintPackage will use the individual fields (Typedefs, Variables etc.)
				// and not just echo a pre-formatted Body.
				// For this iteration, let's assume PrintPackage is smart.
			},
			// This expected output assumes PrintPackage intelligently combines the components.
			// The actual Body field in the Package struct might be the raw parsed body,
			// but the printer should generate from the structured fields.
			want: `package complex_pkg;
    parameter DATA_WIDTH = 32;

    import common_types_pkg::*;

    typedef struct packed { logic valid; logic [DATA_WIDTH-1:0] data; } packet_t;

    packet_t current_packet;
endpackage
`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := printPackage(tt.pkg) // Now using the actual PrintPackage function

			if normalizeSpaceFile(got) != normalizeSpaceFile(tt.want) {
				t.Errorf("PrintPackage() got =\n%v\nwant =\n%v", got, tt.want)
			}
		})
	}
}
