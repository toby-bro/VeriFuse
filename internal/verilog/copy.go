package verilog

func (m *Module) DeepCopy() *Module {
	if m == nil {
		return nil
	}
	copiedModule := &Module{
		Name: m.Name,
		Body: m.Body,
	}

	if m.Ports != nil {
		copiedModule.Ports = make([]Port, len(m.Ports))
		copy(copiedModule.Ports, m.Ports)
	} else {
		copiedModule.Ports = []Port{}
	}

	if m.Parameters != nil {
		copiedModule.Parameters = make([]Parameter, len(m.Parameters))
		copy(copiedModule.Parameters, m.Parameters)
	} else {
		copiedModule.Parameters = []Parameter{}
	}

	return copiedModule
}

func (d *DependencyNode) DeepCopy() *DependencyNode {
	if d == nil {
		return nil
	}
	copiedNode := &DependencyNode{
		Name:      d.Name,
		DependsOn: make([]string, len(d.DependsOn)),
	}
	copy(copiedNode.DependsOn, d.DependsOn)
	return copiedNode
}

func (vf *VerilogFile) DeepCopy() *VerilogFile {
	if vf == nil {
		return nil
	}
	copiedFile := &VerilogFile{
		Name:       vf.Name,
		Modules:    make(map[string]*Module),
		Interfaces: make(map[string]*Interface),

		Classes:       make(map[string]*Class),
		Structs:       make(map[string]*Struct),
		DependancyMap: make(map[string]*DependencyNode),
	}
	for name, module := range vf.Modules {
		copiedFile.Modules[name] = module.DeepCopy()
	}
	for name, iface := range vf.Interfaces {
		copiedFile.Interfaces[name] = iface
	}
	for name, class := range vf.Classes {
		copiedFile.Classes[name] = class
	}
	for name, strct := range vf.Structs {
		copiedFile.Structs[name] = strct
	}
	for name, depNode := range vf.DependancyMap {
		copiedFile.DependancyMap[name] = depNode.DeepCopy()
	}
	return copiedFile
}
