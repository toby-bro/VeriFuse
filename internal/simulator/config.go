package simulator

// Config holds configuration for a simulator type
type Config struct {
	Name      string // Human-readable name for the simulator variant
	WorkDir   string // Subdirectory name within the worker directory
	Prefix    string // Prefix for output files or identifiers
	ErrorName string // Name used in error messages
}

// CommonConfigs provides pre-defined configurations for common simulator setups
var CommonConfigs = struct {
	IVerilog        Config
	IVerilogSV2V    Config
	VerilatorO0     Config
	VerilatorO3     Config
	VerilatorO0SV2V Config
	VerilatorO3SV2V Config
	CXXRTL          Config
	CXXRTLSlang     Config
	CXXRTLSV2V      Config
	CXXRTLSlangSV2V Config
}{
	IVerilog: Config{
		Name:      "icarus",
		WorkDir:   "icarus",
		Prefix:    "iv_",
		ErrorName: "iverilog",
	},
	IVerilogSV2V: Config{
		Name:      "icaru2",
		WorkDir:   "icarus_sv2v",
		Prefix:    "iv2_",
		ErrorName: "iverilog_sv2v",
	},
	VerilatorO0: Config{
		Name:      "vtor01",
		WorkDir:   "vl_O0",
		Prefix:    "vl01_",
		ErrorName: "verilator_O0",
	},
	VerilatorO3: Config{
		Name:      "vtor31",
		WorkDir:   "vl_O3",
		Prefix:    "vl31_",
		ErrorName: "verilator_O3",
	},
	VerilatorO0SV2V: Config{
		Name:      "vtor20",
		WorkDir:   "vl_O0_sv2v",
		Prefix:    "vl20_",
		ErrorName: "verilator_O0_sv2v",
	},
	VerilatorO3SV2V: Config{
		Name:      "vtor23",
		WorkDir:   "vl_O3_sv2v",
		Prefix:    "vl23_",
		ErrorName: "verilator_O3_sv2v",
	},
	CXXRTL: Config{
		Name:      "CXXRTL",
		WorkDir:   "cxxrtl_sim",
		Prefix:    "cxx_vanilla_",
		ErrorName: "CXXRTL",
	},
	CXXRTLSlang: Config{
		Name:      "CXXSLG",
		WorkDir:   "cxxrtl_slang_sim",
		Prefix:    "cxx_slang_",
		ErrorName: "CXXRTL (Slang)",
	},
	CXXRTLSV2V: Config{
		Name:      "CXXRT2",
		WorkDir:   "cxxrtl_sim_sv2v",
		Prefix:    "cxx2_vanilla_",
		ErrorName: "CXXRTL_sv2v",
	},
	CXXRTLSlangSV2V: Config{
		Name:      "CXXSL2",
		WorkDir:   "cxxrtl_slang_sim_sv2v",
		Prefix:    "cxx2_slang_",
		ErrorName: "CXXRTL_slang_sv2v",
	},
}
