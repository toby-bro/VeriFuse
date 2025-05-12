package verilog

type (
	PortDirection int
	PortType      int
)

const (
	INPUT PortDirection = iota
	OUTPUT
	INOUT
	INTERNAL
)

const (
	UNKNOWN PortType = iota
	REG
	WIRE
	INTEGER
	REAL
	TIME
	REALTIME
	LOGIC // SystemVerilog from now
	BIT
	BYTE
	SHORTINT
	INT
	LONGINT
	SHORTREAL
	STRING // sort of reg but you know...
	STRUCT
	VOID
	ENUM
	USERDEFINED
)

type Parameter struct {
	Name         string
	Type         PortType
	DefaultValue string
	Localparam   bool
}

type Port struct {
	Name      string
	Direction PortDirection
	Type      PortType
	Width     int
	IsSigned  bool
}

type Module struct {
	Name       string
	Ports      []Port
	Parameters []Parameter
	Body       string
}

type Variable struct {
	Name         string
	Type         PortType
	Width        int
	Unsigned     bool
	Array        string
	ParentStruct *Struct
	ParentClass  *Class
}

type Struct struct {
	Name      string
	Variables []*Variable
}

// We do NOT support virtual classes and static functions yet
// TODO: #4 Add support for virtual classes and static functions to get parametrized tasks https://stackoverflow.com/questions/57755991/passing-parameters-to-a-verilog-function
type Function struct {
	Name  string
	Ports []Port
	Body  string
}

type Task struct {
	Name  string
	Ports []Port
	Body  string
}

type Class struct {
	Name       string
	Parameters []Parameter
	Body       string
	Tasks      []Task
	Functions  []Function
	isVirtual  bool
	extends    string
}

type ModPort struct {
	Name    string
	Inputs  []string
	Outputs []string
}

type Interface struct {
	Name       string
	Variables  []Variable
	ModPorts   []ModPort
	Parameters []Parameter
	Body       string
}

type VerilogFile struct { //nolint:revive
	Name          string
	Modules       map[string]*Module
	Interfaces    map[string]*Interface
	Classes       map[string]*Class
	Structs       map[string]*Struct
	DependancyMap map[string]*DependencyNode
}

type DependencyNode struct {
	Name      string
	DependsOn []string
}
