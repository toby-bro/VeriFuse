package verilog

import (
	"fmt"
	"strings"
)

func (v *VerilogFile) AddDependency(childName string, parentNames ...string) {
	if v.DependencyMap == nil {
		v.DependencyMap = make(map[string]*DependencyNode)
	}

	if childName == "" {
		return
	}

	childNode, exists := v.DependencyMap[childName]
	if !exists {
		childNode = &DependencyNode{Name: childName}
		v.DependencyMap[childName] = childNode
	}

	for _, parentName := range parentNames {
		if parentName == "" {
			continue
		}

		if parentName == childName {
			continue
		}

		parentNode, exists := v.DependencyMap[parentName]
		if !exists {
			parentNode = &DependencyNode{Name: parentName}
			v.DependencyMap[parentName] = parentNode
		}

		dependencyExists := false
		for _, existing := range childNode.DependsOn {
			if existing == parentName {
				dependencyExists = true
				break
			}
		}

		if !dependencyExists {
			childNode.DependsOn = append(childNode.DependsOn, parentName)
			parentNode.DependedBy = append(parentNode.DependedBy, childName)
		}
	}
}

func (v *VerilogFile) DumpDependencyGraph() string {
	var result string
	for _, node := range v.DependencyMap {
		result += "- " + node.Name + "\n" // nolint: perfsprint
		if len(node.DependsOn) != 0 {
			result += "╭ depends on:\n"
			for _, dep := range node.DependsOn {
				result += fmt.Sprintf("| %s\n", dep) // nolint: perfsprint
			}
		}
		if len(node.DependedBy) != 0 {
			result += "╭ depended by:\n"
			for _, depBy := range node.DependedBy {
				result += fmt.Sprintf("| %s\n", depBy) // nolint: perfsprint
			}
		}
	}
	return result
}

func (s *ScopeNode) Dump(indent int) string {
	if s == nil {
		return ""
	}

	var sb strings.Builder
	var begin string
	if len(s.Children) != 0 || len(s.Variables) != 0 {
		begin = "╭"
	} else {
		begin = "─"
	}
	sb.WriteString(
		fmt.Sprintf("%s%sNode %d:\n", strings.Repeat("│", indent-1), begin, s.Level),
	)
	for _, variable := range s.Variables {
		sb.WriteString(fmt.Sprintf("%s├Variable: %s, Type: %s, Width: %d, Unsigned: %t\n",
			strings.Repeat("│", indent-1),
			variable.Name, variable.Type, variable.Width, variable.Unsigned),
		)
	}
	if len(s.Variables) > 0 {
		sb.WriteString(strings.Repeat("│", indent-1) + "╰End of variables\n")
	}
	for _, child := range s.Children {
		sb.WriteString(child.Dump(indent + 1))
	}
	return sb.String()
}
