package verilog

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
