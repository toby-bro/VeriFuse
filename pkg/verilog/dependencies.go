package verilog

import "fmt"

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
		result += "- " + node.Name + "\n"
		if len(node.DependsOn) != 0 {
			result += "╭ depends on:\n"
			for _, dep := range node.DependsOn {
				result += fmt.Sprintf("| %s\n", dep)
			}
		}
		if len(node.DependedBy) != 0 {
			result += "╭ depended by:\n"
			for _, depBy := range node.DependedBy {
				result += fmt.Sprintf("| %s\n", depBy)
			}
		}
	}
	return result
}
