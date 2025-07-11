package verilog

import (
	"fmt"
	"sort"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// String returns the Verilog keyword for the port direction.
func (d PortDirection) String() string {
	switch d {
	case INPUT:
		return "input"
	case OUTPUT:
		return "output"
	case INOUT:
		return "inout"
	case INTERNAL:
		return "internal" // This might not be a standard Verilog keyword for declarations
	default:
		return fmt.Sprintf("direction_%d", d)
	}
}

// String returns the Verilog keyword for the port type.
func (pt PortType) String() string {
	switch pt {
	case REG:
		return "reg"
	case WIRE:
		return "wire"
	case INTEGER:
		return "integer"
	case REAL:
		return "real"
	case TIME:
		return "time"
	case REALTIME:
		return "realtime"
	case LOGIC:
		return "logic"
	case BIT:
		return "bit"
	case BYTE:
		return "byte"
	case SHORTINT:
		return "shortint"
	case INT:
		return "int"
	case LONGINT:
		return "longint"
	case SHORTREAL:
		return "shortreal"
	case STRING:
		return "string"
	case STRUCT:
		return "struct"
	case VOID:
		return "void"
	case ENUM:
		return "enum"
	case TYPE:
		return "type" // For parameters
	case INTERFACE:
		return "interface" // For interface ports
	case USERDEFINED, UNKNOWN:
		// The String() method for USERDEFINED should indicate it's a placeholder.
		// The actual type name needs to be resolved from context.
		return ""
	default:
		return fmt.Sprintf("type_%d", pt)
	}
}

// formatWidth creates a string representation for port/variable width, e.g., "[7:0]".
// Returns an empty string for scalar (width 1).
func formatWidth(width int) string {
	if width <= 1 {
		return ""
	}
	return fmt.Sprintf("[%d:0]", width-1)
}

func portDirectionToString(d PortDirection) string {
	switch d {
	case INPUT:
		return "input"
	case OUTPUT:
		return "output"
	case INOUT:
		return "inout"
	case INTERNAL:
		return "" // Or decide not to print for INTERNAL
	default:
		return fmt.Sprintf("direction_%d", d) // Fallback
	}
}

func typeToString(pt PortType) string {
	switch pt {
	case REG:
		return "reg"
	case WIRE:
		return "wire"
	case INTEGER:
		return "integer"
	case REAL:
		return "real"
	case TIME:
		return "time"
	case REALTIME:
		return "realtime"
	case LOGIC:
		return "logic"
	case BIT:
		return "bit"
	case BYTE:
		return "byte"
	case SHORTINT:
		return "shortint"
	case INT:
		return "int"
	case LONGINT:
		return "longint"
	case SHORTREAL:
		return "shortreal"
	case STRING:
		return "string"
	case STRUCT:
		// For struct *type*, the name of the struct definition is used.
		// This function is for the keyword.
		return "struct"
	case VOID:
		return "void"
	case ENUM:
		// Similar to struct, "enum" is the keyword.
		return "enum"
	case TYPE:
		return "type" // For parameters
	case INTERFACE:
		return "interface" // For interface ports
	case USERDEFINED, UNKNOWN:
		// This is tricky. The actual user-defined type name should be used.
		// The caller (PrintPort, PrintVariableDeclaration) needs to handle this.
		// Returning a placeholder or expecting resolution before this.
		// For now, let's assume the parser/linker provides the actual name for USERDEFINED types.
		// If this function is called with USERDEFINED, it implies a missing resolution.
		return "" // Or "" if it should be resolved by caller
	default:
		return fmt.Sprintf("type_%d", pt) // Fallback
	}
}

// printParameter formats a Parameter for module/class headers.
func printParameter(param *Parameter, isLast bool) string {
	var sb strings.Builder
	sb.WriteString("parameter ")
	if param.Type != UNKNOWN {
		sb.WriteString(param.Type.String())
		sb.WriteString(" ")
	}
	sb.WriteString(param.Name)
	if param.DefaultValue != "" {
		sb.WriteString(" = ")
		sb.WriteString(param.DefaultValue)
	}
	if param.Width > 1 {
		sb.WriteString(formatWidth(param.Width))
		sb.WriteString(" ")
	}
	if !isLast {
		sb.WriteString(",")
	}
	return sb.String()
}

// printPort formats a Port for module headers.
func printPort(port *Port, isLast bool, ansiStyle bool) string {
	var sb strings.Builder

	// Add pragma if present
	if port.Pragma != "" {
		sb.WriteString("(* ")
		sb.WriteString(port.Pragma)
		sb.WriteString(" *) ")
	}

	if !port.AlreadyDeclared && ansiStyle {
		// Special handling for interface ports
		if port.IsInterfacePort() {
			// For interface ports, print the interface type (e.g., simple_bus.slave)
			sb.WriteString(port.GetInterfaceType())
			sb.WriteString(" ")
		} else {
			// Regular port handling
			if port.Direction != INTERNAL {
				sb.WriteString(portDirectionToString(port.Direction))
				sb.WriteString(" ")
			}

			portTypeStr := typeToString(port.Type)
			if portTypeStr != "" {
				// Avoid printing 'logic' if it's the default and no other specifiers exist,
				// unless it's truly specified. This can be tricky.
				// For simplicity, print what's parsed.
				sb.WriteString(portTypeStr)
				sb.WriteString(" ")
			}

			if port.IsSigned {
				sb.WriteString("signed ")
			}

			widthStr := formatWidth(port.Width)
			if widthStr != "" {
				sb.WriteString(widthStr)
				sb.WriteString(" ")
			}
		}
	}

	sb.WriteString(port.Name)
	if port.Array != "" {
		sb.WriteString("[" + port.Array + "]")
	}
	if !isLast {
		sb.WriteString(",")
	}
	return sb.String()
}

// printVariableDeclaration formats a Variable declaration (for structs, etc.).
func printVariableDeclaration(v *Variable) string {
	var sb strings.Builder
	typeStr := typeToString(v.Type)
	if v.Type == USERDEFINED {
		// This part needs to be smarter, potentially looking up the actual type name
		// from a VerilogFile context if the variable's Type field doesn't store the name.
		// For now, assuming typeStr from PortTypeToString might be "userdefined"
		// or the actual name if the parser sets it directly.
		// If v.Type is USERDEFINED, the actual type name should be stored somewhere,
		// e.g. in a separate string field in the Variable struct, or resolved via ParentStruct/Class.
		if v.ParentStruct != nil { // Example: if Variable has a direct link
			typeStr = v.ParentStruct.Name
		} else if v.ParentClass != nil {
			typeStr = v.ParentClass.Name
		}
		// If not, PortTypeToString(USERDEFINED) might return "userdefined"
		// which is not a valid Verilog type. The parser/linker should ensure
		// user-defined types are resolved to their names.
	}

	sb.WriteString(typeStr)
	sb.WriteString(" ")

	if v.Unsigned &&
		(v.Type == INTEGER || v.Type == INT || v.Type == LONGINT || v.Type == SHORTINT || v.Type == BYTE) {
		sb.WriteString("unsigned ")
	}

	widthStr := formatWidth(v.Width)
	if widthStr != "" {
		sb.WriteString(widthStr)
		sb.WriteString(" ")
	}
	sb.WriteString(v.Name)

	// TODO: Add array printing if v.Array is populated, e.g., `[size1][size2]`

	sb.WriteString(";")
	return sb.String()
}

// printStruct converts a Struct object to its Verilog string representation.
func printStruct(s *Struct) string {
	var sb strings.Builder
	sb.WriteString("typedef struct packed {\n")
	for _, variable := range s.Variables {
		sb.WriteString("    ")
		sb.WriteString(
			printVariableDeclaration(variable),
		) // Assumes PrintVariableDeclaration is suitable
		sb.WriteString("\n")
	}
	sb.WriteString("} ")
	sb.WriteString(s.Name)
	sb.WriteString(";\n")
	return sb.String()
}

// printInterfacePort formats an InterfacePort for interface port declarations.
func printInterfacePort(port *InterfacePort, isLast bool) string {
	var sb strings.Builder

	// Add pragma if present
	if port.Pragma != "" {
		sb.WriteString("(* ")
		sb.WriteString(port.Pragma)
		sb.WriteString(" *) ")
	}

	if port.Direction != INTERNAL {
		sb.WriteString(portDirectionToString(port.Direction))
		sb.WriteString(" ")
	}

	portTypeStr := typeToString(port.Type)
	if portTypeStr != "" {
		sb.WriteString(portTypeStr)
		sb.WriteString(" ")
	}

	if port.IsSigned {
		sb.WriteString("signed ")
	}

	widthStr := formatWidth(port.Width)
	if widthStr != "" {
		sb.WriteString(widthStr)
		sb.WriteString(" ")
	}

	sb.WriteString(port.Name)
	if !isLast {
		sb.WriteString(",")
	}
	return sb.String()
}

// printModPort formats a ModPort declaration for interfaces.
func printModPort(modport *ModPort) string {
	return printModPortWithIndent(modport, "")
}

// printModPortWithIndent formats a ModPort declaration with specified indentation
func printModPortWithIndent(modport *ModPort, indent string) string {
	var sb strings.Builder
	sb.WriteString(indent)
	sb.WriteString("modport ")
	sb.WriteString(modport.Name)
	sb.WriteString(" (\n")

	for i, signal := range modport.Signals {
		sb.WriteString(indent)
		sb.WriteString("    ") // 4 additional spaces for signal indentation
		sb.WriteString(portDirectionToString(signal.Direction))
		sb.WriteString(" ")
		sb.WriteString(signal.Name)
		if i < len(modport.Signals)-1 {
			sb.WriteString(",")
		}
		sb.WriteString("\n")
	}

	sb.WriteString(indent)
	sb.WriteString(");") // Closing parenthesis at same level as modport keyword
	return sb.String()
}

func printInterface(i *Interface) string {
	var sb strings.Builder

	// Handle virtual interfaces
	if i.IsVirtual {
		sb.WriteString("virtual ")
	}

	sb.WriteString("interface ")
	sb.WriteString(i.Name)

	// Handle parameters
	if len(i.Parameters) > 0 {
		sb.WriteString(" #(\n")
		for j, param := range i.Parameters {
			sb.WriteString("    ")
			sb.WriteString(printParameter(param, j == len(i.Parameters)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}

	// Handle interface ports (input/output ports of the interface itself)
	if len(i.Ports) > 0 {
		sb.WriteString(" (\n")
		for j, port := range i.Ports {
			sb.WriteString("    ")
			sb.WriteString(printInterfacePort(port, j == len(i.Ports)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}

	// Handle extends
	if i.ExtendsFrom != "" {
		sb.WriteString(" extends ")
		sb.WriteString(i.ExtendsFrom)
	}

	sb.WriteString(";\n")

	// Two approaches based on body content:
	// 1. If body is empty/nil, generate the body from components
	// 2. If body is a string, just print the body directly
	if strings.TrimSpace(i.Body) != "" {
		// Approach 2: Body contains parsed content, print it directly
		bodyLines := strings.Split(i.Body, "\n")
		for _, line := range bodyLines {
			if strings.TrimSpace(line) != "" {
				// Check if line already has proper indentation
				if strings.HasPrefix(line, "    ") {
					sb.WriteString(line)
				} else {
					sb.WriteString("    ")
					sb.WriteString(line)
				}
				sb.WriteString("\n")
			}
		}
	} else {
		// Approach 1: Body is empty, generate from components
		// Print variables declared in the interface
		if len(i.Variables) > 0 {
			for _, variable := range i.Variables {
				sb.WriteString("    ")
				sb.WriteString(printVariableDeclaration(variable))
				sb.WriteString("\n")
			}
			if len(i.ModPorts) > 0 {
				sb.WriteString("\n") // Add spacing before modports
			}
		}

		// Print modport declarations
		if len(i.ModPorts) > 0 {
			for j, modport := range i.ModPorts {
				sb.WriteString(printModPortWithIndent(modport, "    "))
				if j < len(i.ModPorts)-1 {
					sb.WriteString("\n\n") // Add spacing between modports
				} else {
					sb.WriteString("\n")
				}
			}
		}
	}

	sb.WriteString("endinterface")
	return sb.String()
}

// printClass converts a Class object to its Verilog string representation.
func printClass(c *Class) string {
	var sb strings.Builder
	if c.isVirtual {
		sb.WriteString("virtual ")
	}
	sb.WriteString("class ")
	sb.WriteString(c.Name)

	if c.extends != "" {
		sb.WriteString(" extends ")
		sb.WriteString(c.extends)
	}

	if len(c.Parameters) > 0 {
		sb.WriteString(" #(\n")
		for i, param := range c.Parameters {
			sb.WriteString("    ")
			sb.WriteString(printParameter(param, i == len(c.Parameters)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}
	sb.WriteString(";\n")

	sb.WriteString(c.Body)

	sb.WriteString("endclass\n")
	return sb.String()
}

// printModule converts a Module object to its Verilog string representation.
func printModule(m *Module) string {
	var sb strings.Builder
	sb.WriteString("module ")
	sb.WriteString(m.Name)

	// Only print ANSI-style parameters in the header
	ansiParams := []*Parameter{}
	for _, param := range m.Parameters {
		if param.AnsiStyle {
			ansiParams = append(ansiParams, param)
		}
	}

	// sort ansiParams by name for consistent output
	sort.Slice(ansiParams, func(i, j int) bool {
		return ansiParams[i].Name < ansiParams[j].Name
	})

	// sort m.Ports by direction and then by name for consistent output
	sort.Slice(m.Ports, func(i, j int) bool {
		if m.Ports[i].Direction != m.Ports[j].Direction {
			return m.Ports[i].Direction < m.Ports[j].Direction
		}
		return m.Ports[i].Name < m.Ports[j].Name
	})

	if len(ansiParams) > 0 {
		sb.WriteString(" #(\n")
		for i, param := range ansiParams {
			sb.WriteString("    ")
			sb.WriteString(printParameter(param, i == len(ansiParams)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}

	if len(m.Ports) > 0 {
		sb.WriteString(" (\n")
		for i, port := range m.Ports {
			sb.WriteString("    ")
			sb.WriteString(printPort(port, i == len(m.Ports)-1, m.AnsiStyle))
			sb.WriteString("\n")
		}
		sb.WriteString(");\n")
	} else {
		sb.WriteString("();\n") // ANSI style for module with no ports
	}

	if m.Body != "" {
		sb.WriteString(utils.TrimEmptyLines(m.Body))
	}

	sb.WriteString("\nendmodule\n")
	return sb.String()
}

// printPackage converts a Package object to its Verilog string representation.
func printPackage(pkg *Package) string {
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf("package %s;\n", pkg.Name))

	// Print Parameters
	if len(pkg.Parameters) > 0 {
		for _, param := range pkg.Parameters {
			// Assuming PrintParameter handles commas correctly if we adapt it or use a helper
			// For simplicity, let's assume parameters are printed one per line without trailing commas here.
			if param.Type != UNKNOWN {
				sb.WriteString(
					fmt.Sprintf(
						"    parameter %s %s = %s;\n",
						param.Type.String(),
						param.Name,
						param.DefaultValue,
					),
				)
			} else {
				sb.WriteString(fmt.Sprintf("    parameter %s = %s;\n", param.Name, param.DefaultValue))
			}
		}
		sb.WriteString("\n") // Add a newline after parameters if any
	}

	// Print Imports
	if len(pkg.Imports) > 0 {
		for _, imp := range pkg.Imports {
			sb.WriteString(fmt.Sprintf("    %s\n", imp))
		}
		sb.WriteString("\n") // Add a newline after imports if any
	}

	// Print Typedefs
	if len(pkg.Typedefs) > 0 {
		for _, typedef := range pkg.Typedefs {
			sb.WriteString(fmt.Sprintf("    %s\n", typedef))
		}
		sb.WriteString("\n") // Add a newline after typedefs if any
	}

	// Print Variables
	if len(pkg.Variables) > 0 {
		for _, v := range pkg.Variables {
			sb.WriteString(fmt.Sprintf("    %s\n", printVariableDeclaration(v)))
		}
		sb.WriteString("\n") // Add a newline after variables if any
	}

	// If there was no content (params, imports, typedefs, vars),
	// and Body is also empty, we might want to ensure there's at least one newline
	// before endpackage, or that the package body isn't just empty.
	// However, the current structure with newlines after each section should handle this.

	// Fallback to Body if it's not empty and other elements were not printed
	// This part is tricky: should we print Body if other elements are present?
	// For now, let's assume if Parameters, Imports, Typedefs, Variables are populated,
	// they are the source of truth. If they are empty, but Body is not, print Body.
	if len(pkg.Parameters) == 0 && len(pkg.Imports) == 0 && len(pkg.Typedefs) == 0 &&
		len(pkg.Variables) == 0 &&
		pkg.Body != "" {
		bodyLines := strings.Split(strings.TrimSpace(pkg.Body), "\n")
		for _, line := range bodyLines {
			sb.WriteString(fmt.Sprintf("    %s\n", strings.TrimSpace(line)))
		}
	}

	sb.WriteString("endpackage\n")
	return sb.String()
}

// getPrintOrder determines the order for printing Verilog elements based on dependencies.
func getPrintOrder(vf *VerilogFile) ([]string, error) { // nolint: gocyclo
	allNodes := make(map[string][]string)
	nodeType := make(map[string]string) // "struct", "class", "module", "interface"

	if vf.DependencyMap == nil {
		var names []string
		for name := range vf.Structs {
			names = append(names, name)
		}
		for name := range vf.Classes {
			names = append(names, name)
		}
		// for name := range vf.Interfaces { names = append(names, name) } // TODO
		for name := range vf.Modules {
			names = append(names, name)
		}
		// Default order if no dependency map
		return names, nil
	}

	for name, node := range vf.DependencyMap {
		allNodes[name] = append([]string{}, node.DependsOn...) // Make a copy
		if _, ok := vf.Structs[name]; ok {
			nodeType[name] = "struct"
		} else if _, ok := vf.Classes[name]; ok {
			nodeType[name] = "class"
		} else if _, ok := vf.Interfaces[name]; ok {
			nodeType[name] = "interface"
		} else if _, ok := vf.Modules[name]; ok {
			nodeType[name] = "module"
		} else if _, ok := vf.Packages[name]; ok { // Added Package type
			nodeType[name] = "package"
		} else {
			continue
			// This node might be an external dependency not defined in this file.
			// Or it's a type not yet handled (e.g. enum, package)
			// For sorting, we only care about nodes defined in *this* VerilogFile.
		}
	}

	// Kahn's algorithm for topological sort
	inDegree := make(map[string]int)
	graph := make(map[string][]string)

	// Initialize inDegree and graph for nodes present in the VerilogFile
	for name := range vf.Structs {
		inDegree[name] = 0
		graph[name] = []string{}
	}
	for name := range vf.Classes {
		inDegree[name] = 0
		graph[name] = []string{}
	}
	for name := range vf.Interfaces { // Corrected from // TODO
		inDegree[name] = 0
		graph[name] = []string{}
	}
	for name := range vf.Modules {
		inDegree[name] = 0
		graph[name] = []string{}
	}
	for name := range vf.Packages { // Added Packages
		inDegree[name] = 0
		graph[name] = []string{}
	}

	for name, deps := range allNodes {
		// Only consider nodes that are actually defined in this VerilogFile
		if _, defined := inDegree[name]; !defined {
			continue
		}
		for _, depName := range deps {
			// If depName is defined in this file, add edge
			if _, definedDep := inDegree[depName]; definedDep {
				graph[depName] = append(graph[depName], name)
				inDegree[name]++
			}
			// If depName is not defined in this file, it's an external dependency.
			// We assume external dependencies are met.
		}
	}

	queue := []string{}
	for name, degree := range inDegree {
		if degree == 0 {
			queue = append(queue, name)
		}
	}
	sort.Strings(queue) // Sort for deterministic output

	var sortedList []string
	for len(queue) > 0 {
		u := queue[0]
		queue = queue[1:]
		sortedList = append(sortedList, u)

		dependents := graph[u]
		sort.Strings(dependents) // Sort for deterministic output

		for _, v := range dependents {
			inDegree[v]--
			if inDegree[v] == 0 {
				queue = append(queue, v)
			}
		}
		sort.Strings(queue) // Keep queue sorted
	}

	// Check if all defined nodes were sorted
	definedNodeCount := len(
		vf.Structs,
	) + len(
		vf.Classes,
	) + len(
		vf.Modules,
	) + len(
		vf.Interfaces,
	) + len(
		vf.Packages,
	) // Added Packages
	if len(sortedList) != definedNodeCount {
		// This indicates a cycle among the defined elements, or an issue with dependency tracking.
		logger.Warn(
			"Topological sort incomplete. Sorted: %d, Defined: %d. Possible cycle or missing internal dependency link.\n",
			len(sortedList),
			definedNodeCount,
		)

		// Fallback: append any missing items to ensure they are printed.
		isSorted := make(map[string]bool)
		for _, name := range sortedList {
			isSorted[name] = true
		}

		appendIfMissing := func(name string) {
			if !isSorted[name] {
				sortedList = append(sortedList, name)
				isSorted[name] = true
			}
		}
		for name := range vf.Structs { // Structs first
			appendIfMissing(name)
		}
		for name := range vf.Interfaces { // Then Interfaces
			appendIfMissing(name)
		}
		for name := range vf.Classes { // Then Classes
			appendIfMissing(name)
		}
		for name := range vf.Modules { // Finally Modules
			appendIfMissing(name)
		}
		for name := range vf.Packages { // Packages first (or based on typical usage)
			appendIfMissing(name)
		}
	}

	return sortedList, nil
}

// PrintVerilogFile converts a VerilogFile object to its string representation.
// It attempts to print definitions in a dependency-aware order.
func PrintVerilogFile(vf *VerilogFile) (string, error) { // nolint: gocyclo
	var sb strings.Builder

	sortedNames, err := getPrintOrder(vf)
	if err != nil {
		// This error from getPrintOrder might indicate cycles, so printing order could be problematic.
		// However, getPrintOrder now tries to return a list even with issues.
		logger.Warn(
			"Problem obtaining print order: %v. Proceeding with potentially incomplete/incorrect order.\n",
			err,
		)
	}
	if len(sortedNames) == 0 &&
		(len(vf.Structs) > 0 || len(vf.Classes) > 0 || len(vf.Interfaces) > 0 || len(vf.Modules) > 0) {
		// If sortedNames is empty but there are items, it means getPrintOrder had a major issue or no deps were found.
		// Fallback to a default order.
		logger.Warn(
			"Print order is empty, falling back to default printing order (Structs, Interfaces, Classes, Modules).",
		)
		// Clear sortedNames to rebuild it in the desired fallback order
		sortedNames = []string{}
		for _, s := range vf.Structs {
			sortedNames = append(sortedNames, s.Name)
		}
		for _, i := range vf.Interfaces {
			sortedNames = append(sortedNames, i.Name)
		}
		for _, c := range vf.Classes {
			sortedNames = append(sortedNames, c.Name)
		}
		for _, m := range vf.Modules {
			sortedNames = append(sortedNames, m.Name)
		}
	}

	printed := make(map[string]bool)

	// Print items from sortedNames in strict categorical order: Structs, Interfaces, Classes, Modules
	// Pass 1: Print Packages from sortedNames
	for _, name := range sortedNames {
		if pkg, ok := vf.Packages[name]; ok && !printed[name] {
			sb.WriteString(printPackage(pkg))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Pass 2: Print Structs from sortedNames
	for _, name := range sortedNames {
		if s, ok := vf.Structs[name]; ok && !printed[name] {
			sb.WriteString(printStruct(s))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Pass 3: Print Interfaces from sortedNames
	for _, name := range sortedNames {
		if i, ok := vf.Interfaces[name]; ok && !printed[name] {
			sb.WriteString(printInterface(i))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Pass 4: Print Classes from sortedNames
	for _, name := range sortedNames {
		if c, ok := vf.Classes[name]; ok && !printed[name] {
			sb.WriteString(printClass(c))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Pass 5: Print Modules from sortedNames
	for _, name := range sortedNames {
		if m, ok := vf.Modules[name]; ok && !printed[name] {
			sb.WriteString(printModule(m))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Ensure everything gets printed, even if not in sortedNames (e.g., if dependency map was incomplete or getPrintOrder missed something)
	// Iterate through all known items in the desired final order.
	// Print remaining Packages
	for name, pkg := range vf.Packages {
		if !printed[name] {
			sb.WriteString(printPackage(pkg))
			sb.WriteString("\n")
			printed[name] = true
			logger.Debug("Printed remaining (unsorted/missed) package: %s\n", name)
		}
	}
	// Print remaining Structs
	for name, s := range vf.Structs {
		if !printed[name] {
			sb.WriteString(printStruct(s))
			sb.WriteString("\n")
			printed[name] = true
			logger.Debug("Printed remaining (unsorted/missed) struct: %s\n", name)
		}
	}
	// Print remaining Interfaces
	for name, i := range vf.Interfaces {
		if !printed[name] {
			sb.WriteString(printInterface(i))
			sb.WriteString("\n")
			printed[name] = true
			logger.Debug("Printed remaining (unsorted/missed) interface: %s\n", name)
		}
	}
	// Print remaining Classes
	for name, c := range vf.Classes {
		if !printed[name] {
			sb.WriteString(printClass(c))
			sb.WriteString("\n")
			printed[name] = true
			logger.Debug("Printed remaining (unsorted/missed) class: %s\n", name)
		}
	}
	// Print remaining Modules
	for name, m := range vf.Modules {
		if !printed[name] {
			sb.WriteString(printModule(m))
			sb.WriteString("\n")
			printed[name] = true
			logger.Debug("Printed remaining (unsorted/missed) module: %s\n", name)
		}
	}

	return sb.String(), nil
}
