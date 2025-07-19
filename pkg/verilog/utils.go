package verilog

func (vf *VerilogFile) CreateModule(name string) *Module {
	if vf.Modules == nil {
		vf.Modules = make(map[string]*Module)
	}
	module := &Module{
		Name:       name,
		Ports:      []*Port{},
		Parameters: []*Parameter{},
		Body:       "",
		AnsiStyle:  true,
	}
	vf.Modules[name] = module
	vf.DependencyMap[name] = &DependencyNode{
		Name:       name,
		DependsOn:  []string{},
		DependedBy: []string{},
	}
	return module
}
