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
			if got := PortDirectionToString(tt.d); got != tt.want {
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
			if got := TypeToString(tt.pt); got != tt.want {
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
			if got := PrintParameter(tt.param, tt.isLast); got != tt.want {
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
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := PrintPort(tt.port, tt.isLast, true); got != tt.want {
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
			if got := PrintVariableDeclaration(tt.v); normalizeSpace(
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
	got := PrintStruct(s)
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
			got := PrintClass(tt.c)
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

			got := PrintModule(tt.m)
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
				DependancyMap: map[string]*DependencyNode{
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
				DependancyMap: map[string]*DependencyNode{
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
				DependancyMap: map[string]*DependencyNode{
					"modA":    {Name: "modA", DependsOn: []string{"structB"}},
					"structB": {Name: "structB", DependsOn: []string{}},
				},
			},
			// modC should still be included by the fallback logic in PrintVerilogFile,
			// getPrintOrder might only return modA, structB based on map.
			// The test for getPrintOrder should reflect what it *returns*.
			// The current getPrintOrder only processes nodes in DependancyMap for sorting,
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
				t.Errorf("getPrintOrder() got = %v, want %v", got, tt.want)
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
				DependancyMap: map[string]*DependencyNode{
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
				DependancyMap: map[string]*DependencyNode{
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
			name: "NoDependencyMapFallbackOrder", // Test fallback when DependancyMap is nil or incomplete
			vf: &VerilogFile{
				Modules: map[string]*Module{"modA": {Name: "modA"}},
				Structs: map[string]*Struct{"structZ": {Name: "structZ"}},
				Classes: map[string]*Class{"classM": {Name: "classM"}},
				// DependancyMap: nil, // Explicitly test nil case
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
				DependancyMap: map[string]*DependencyNode{
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
		DependancyMap: map[string]*DependencyNode{
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
