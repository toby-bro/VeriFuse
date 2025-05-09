package verilog

import (
	"fmt"
	"sort"
	"strings"
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

func PortDirectionToString(d PortDirection) string {
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

func TypeToString(pt PortType) string {
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

// PrintParameter formats a Parameter for module/class headers.
func PrintParameter(param Parameter, isLast bool) string {
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
	if !isLast {
		sb.WriteString(",")
	}
	return sb.String()
}

// PrintPort formats a Port for module headers.
func PrintPort(port Port, isLast bool) string {
	var sb strings.Builder
	if port.Direction != INTERNAL {
		sb.WriteString(PortDirectionToString(port.Direction))
		sb.WriteString(" ")
	}

	portTypeStr := TypeToString(port.Type)
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

	sb.WriteString(port.Name)
	if !isLast {
		sb.WriteString(",")
	}
	return sb.String()
}

// PrintVariableDeclaration formats a Variable declaration (for structs, etc.).
func PrintVariableDeclaration(v *Variable) string {
	var sb strings.Builder
	typeStr := TypeToString(v.Type)
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

// PrintStruct converts a Struct object to its Verilog string representation.
func PrintStruct(s *Struct) string {
	var sb strings.Builder
	sb.WriteString("typedef struct packed {\n")
	for _, variable := range s.Variables {
		sb.WriteString("    ")
		sb.WriteString(
			PrintVariableDeclaration(variable),
		) // Assumes PrintVariableDeclaration is suitable
		sb.WriteString("\n")
	}
	sb.WriteString("} ")
	sb.WriteString(s.Name)
	sb.WriteString(";\n")
	return sb.String()
}

// PrintClass converts a Class object to its Verilog string representation.
func PrintClass(c *Class) string {
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
			sb.WriteString(PrintParameter(param, i == len(c.Parameters)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}
	sb.WriteString(";\n")

	indentedBody := ""
	if strings.TrimSpace(c.Body) != "" {
		for _, line := range strings.Split(c.Body, "\n") {
			if strings.TrimSpace(line) != "" {
				indentedBody += "    " + line + "\n"
			}
		}
	}
	sb.WriteString(indentedBody)

	sb.WriteString("endclass\n")
	return sb.String()
}

// PrintModule converts a Module object to its Verilog string representation.
func PrintModule(m *Module) string {
	var sb strings.Builder
	sb.WriteString("module ")
	sb.WriteString(m.Name)

	if len(m.Parameters) > 0 {
		sb.WriteString(" #(\n")
		for i, param := range m.Parameters {
			sb.WriteString("    ")
			sb.WriteString(PrintParameter(param, i == len(m.Parameters)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(")")
	}

	if len(m.Ports) > 0 {
		sb.WriteString(" (\n")
		for i, port := range m.Ports {
			sb.WriteString("    ")
			sb.WriteString(PrintPort(port, i == len(m.Ports)-1))
			sb.WriteString("\n")
		}
		sb.WriteString(");\n")
	} else {
		sb.WriteString("();\n") // ANSI style for module with no ports
	}

	bodyToPrint := strings.TrimSpace(m.Body)
	if bodyToPrint != "" {
		var indentedBody strings.Builder
		for _, line := range strings.Split(bodyToPrint, "\n") {
			// Avoid double indenting if lines in body are already indented.
			// This simple indent might not be perfect if body has mixed indentation.
			if strings.HasPrefix(line, "    ") {
				indentedBody.WriteString(line)
			} else {
				indentedBody.WriteString("    ")
				indentedBody.WriteString(line)
			}
			indentedBody.WriteString("\n")
		}
		sb.WriteString(indentedBody.String())
	}

	sb.WriteString("endmodule\n")
	return sb.String()
}

// getPrintOrder determines the order for printing Verilog elements based on dependencies.
func getPrintOrder(vf *VerilogFile) ([]string, error) {
	allNodes := make(map[string][]string)
	nodeType := make(map[string]string) // "struct", "class", "module", "interface"

	if vf.DependancyMap == nil {
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

	for name, node := range vf.DependancyMap {
		allNodes[name] = append([]string{}, node.DependsOn...) // Make a copy
		if _, ok := vf.Structs[name]; ok {
			nodeType[name] = "struct"
		} else if _, ok := vf.Classes[name]; ok {
			nodeType[name] = "class"
			// } else if _, ok := vf.Interfaces[name]; ok { // TODO
			//     nodeType[name] = "interface"
		} else if _, ok := vf.Modules[name]; ok {
			nodeType[name] = "module"
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
	// for name := range vf.Interfaces { inDegree[name] = 0; graph[name] = []string{} } // TODO
	for name := range vf.Modules {
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
	definedNodeCount := len(vf.Structs) + len(vf.Classes) + len(vf.Modules) // + len(vf.Interfaces)
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
		for name := range vf.Structs {
			appendIfMissing(name)
		}
		for name := range vf.Classes {
			appendIfMissing(name)
		}
		// for name := range vf.Interfaces { appendIfMissing(name) } // TODO
		for name := range vf.Modules {
			appendIfMissing(name)
		}
	}

	return sortedList, nil
}

// PrintVerilogFile converts a VerilogFile object to its string representation.
// It attempts to print definitions in a dependency-aware order.
func PrintVerilogFile(vf *VerilogFile) (string, error) {
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
		(len(vf.Structs) > 0 || len(vf.Classes) > 0 || len(vf.Modules) > 0) {
		// If sortedNames is empty but there are items, it means getPrintOrder had a major issue or no deps were found.
		// Fallback to a default order.
		logger.Warn(
			"Print order is empty, falling back to default printing order (Structs, Classes, Modules).",
		)
		for _, s := range vf.Structs {
			sortedNames = append(sortedNames, s.Name)
		}
		for _, c := range vf.Classes {
			sortedNames = append(sortedNames, c.Name)
		}
		// for _, i := range vf.Interfaces { sortedNames = append(sortedNames, i.Name) } // TODO
		for _, m := range vf.Modules {
			sortedNames = append(sortedNames, m.Name)
		}
	}

	printed := make(map[string]bool)

	for _, name := range sortedNames {
		if printed[name] {
			continue
		}
		if s, ok := vf.Structs[name]; ok {
			sb.WriteString(PrintStruct(s))
			sb.WriteString("\n")
			printed[name] = true
		} else if c, ok := vf.Classes[name]; ok {
			sb.WriteString(PrintClass(c))
			sb.WriteString("\n")
			printed[name] = true
			// } else if i, ok := vf.Interfaces[name]; ok { // TODO: Implement PrintInterface if needed
			// 	sb.WriteString(PrintInterface(i)) // Assuming PrintInterface exists
			// 	sb.WriteString("\n")
			//  printed[name] = true
		} else if m, ok := vf.Modules[name]; ok {
			sb.WriteString(PrintModule(m))
			sb.WriteString("\n")
			printed[name] = true
		}
	}

	// Ensure everything gets printed, even if not in sortedNames (e.g., if dependency map was incomplete)
	printRemaining := func(collectionType string) {
		switch collectionType {
		case "struct":
			for name, s := range vf.Structs {
				if !printed[name] {
					sb.WriteString(PrintStruct(s))
					sb.WriteString("\n")
					printed[name] = true
					logger.Debug("Printed remaining struct: %s\n", name)
				}
			}
		case "class":
			for name, c := range vf.Classes {
				if !printed[name] {
					sb.WriteString(PrintClass(c))
					sb.WriteString("\n")
					printed[name] = true
					logger.Debug("Printed remaining class: %s\n", name)
				}
			}
		// case "interface":
		// for name, i := range vf.Interfaces { if !printed[name] { sb.WriteString(PrintInterface(i)); sb.WriteString("\n"); printed[name] = true } }
		case "module":
			for name, m := range vf.Modules {
				if !printed[name] {
					sb.WriteString(PrintModule(m))
					sb.WriteString("\n")
					printed[name] = true
					logger.Debug("Printed remaining module: %s\n", name)
				}
			}
		}
	}
	printRemaining("struct")
	printRemaining("class")
	// printRemaining("interface")
	printRemaining("module")

	return sb.String(), nil
}
