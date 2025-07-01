package verilog

type (
	PortDirection int
	PortType      int
	ClockEdge     int
	TimingUnit    int
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
	TYPE      // Only for parameters
	INTERFACE // Interface ports (e.g., simple_bus.slave)
)

const (
	POSEDGE ClockEdge = iota
	NEGEDGE
	BOTHEDGE
)

const (
	NANOSECOND TimingUnit = iota
	PICOSECOND
	FEMTOSECOND
	TIMEUNIT
)

// ModPortSignal represents a signal within a modport with its direction
type ModPortSignal struct {
	Name      string
	Direction PortDirection
}

// InterfacePort represents input/output ports of an interface (like module ports)
type InterfacePort struct {
	Name      string
	Direction PortDirection
	Type      PortType
	Width     int
	IsSigned  bool
	Array     string
	Pragma    string
}

type Parameter struct {
	Name         string
	Type         PortType
	DefaultValue string
	Localparam   bool
	Width        int
	AnsiStyle    bool
}

type Port struct {
	Name            string
	Direction       PortDirection
	Type            PortType
	Width           int
	IsSigned        bool
	AlreadyDeclared bool
	Array           string
	Pragma          string // pragma information if any
	// Interface port information
	InterfaceName string // Name of the interface (e.g., "simple_bus")
	ModportName   string // Name of the modport (e.g., "slave", "master")
}

// IsInterfacePort returns true if this port is an interface port
func (p *Port) IsInterfacePort() bool {
	return p.InterfaceName != "" && p.ModportName != ""
}

// GetInterfaceType returns the full interface type string (e.g., "simple_bus.slave")
func (p *Port) GetInterfaceType() string {
	if p.IsInterfacePort() {
		return p.InterfaceName + "." + p.ModportName
	}
	return ""
}

type Module struct {
	Name       string
	Ports      []Port
	Parameters []Parameter
	Body       string
	AnsiStyle  bool
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

// ScopeVariable extends Variable with usage tracking for scope analysis
type ScopeVariable struct {
	*Variable
	Blocked bool // true if variable is already used as output and can only be used as input
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

type Package struct {
	Name       string
	Body       string
	Typedefs   []string    // typedef statements found in package
	Imports    []string    // import statements that this package makes
	Variables  []*Variable // Variables declared in the package
	Parameters []Parameter // Parameters if any
}

type ModPort struct {
	Name    string
	Signals []ModPortSignal
}

type Interface struct {
	Name        string
	Ports       []InterfacePort // Interface can have its own input/output ports
	Parameters  []Parameter     // Interface parameters
	ModPorts    []ModPort       // Modport declarations
	Variables   []*Variable     // Variables declared in the interface
	Body        string          // Raw body content for unparsed elements
	IsVirtual   bool            // Whether this is a virtual interface
	ExtendsFrom string          // Name of interface this extends from (if any)
}

type VerilogFile struct { //nolint:revive
	Name          string
	Modules       map[string]*Module
	Interfaces    map[string]*Interface
	Classes       map[string]*Class
	Structs       map[string]*Struct
	Packages      map[string]*Package
	DependencyMap map[string]*DependencyNode
}

type DependencyNode struct {
	Name       string
	DependsOn  []string
	DependedBy []string
}

type ScopeNode struct {
	Level     int
	Variables map[string]*ScopeVariable
	Children  []*ScopeNode
	Parent    *ScopeNode
	LastLine  int
}

func NewVerilogFile(name string) *VerilogFile {
	return &VerilogFile{
		Name:          name,
		Modules:       make(map[string]*Module),
		Interfaces:    make(map[string]*Interface),
		Classes:       make(map[string]*Class),
		Structs:       make(map[string]*Struct),
		Packages:      make(map[string]*Package),
		DependencyMap: make(map[string]*DependencyNode),
	}
}
