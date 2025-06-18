package verilogExt

import (
	"regexp"

	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// This is loads of useless Copilot generated code, but that might come in handly one day so I did not purge it yet.

// ===============================================
// Advanced SystemVerilog Construct Regex Patterns
// ===============================================

// Generate block patterns for complex generate statements
var generateBlockRegex = regexp.MustCompile(
	`(?s)(?:^|\s)generate\s+(.*?)\s+endgenerate`,
)

var generateIfRegex = regexp.MustCompile(
	`(?s)(?:^|\s)if\s*\((.*?)\)\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end(?:\s+else\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end)?`,
)

var generateForRegex = regexp.MustCompile(
	`(?s)(?:^|\s)for\s*\((.*?)\)\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end`,
)

var generateCaseRegex = regexp.MustCompile(
	`(?s)(?:^|\s)case\s*\((.*?)\)\s+(.*?)\s+endcase`,
)

// Always block patterns for complex always blocks with sensitivity lists
var alwaysBlockRegex = regexp.MustCompile(
	`(?s)(?:^|\s)(always|always_comb|always_ff|always_latch)(?:\s*@\s*\((.*?)\))?\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end`,
)

var alwaysCombRegex = regexp.MustCompile(
	`(?s)(?:^|\s)always_comb\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end`,
)

var alwaysFFRegex = regexp.MustCompile(
	`(?s)(?:^|\s)always_ff\s*@\s*\((.*?)\)\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end`,
)

var alwaysLatchRegex = regexp.MustCompile(
	`(?s)(?:^|\s)always_latch\s*@\s*\((.*?)\)\s+begin(?:\s*:\s*(\w+))?\s+(.*?)\s+end`,
)

// SystemVerilog assertion patterns (assert, assume, cover, restrict properties)
var assertPropertyRegex = regexp.MustCompile(
	`(?s)(?:^|\s)assert\s+property\s*\((.*?)\)(?:\s+else\s+(.*?))?(?:\s*;)?`,
)

var assumePropertyRegex = regexp.MustCompile(
	`(?s)(?:^|\s)assume\s+property\s*\((.*?)\)(?:\s+else\s+(.*?))?(?:\s*;)?`,
)

var coverPropertyRegex = regexp.MustCompile(
	`(?s)(?:^|\s)cover\s+property\s*\((.*?)\)(?:\s*;)?`,
)

var restrictPropertyRegex = regexp.MustCompile(
	`(?s)(?:^|\s)restrict\s+property\s*\((.*?)\)(?:\s*;)?`,
)

var assertStatementRegex = regexp.MustCompile(
	`(?s)(?:^|\s)assert\s*\((.*?)\)(?:\s+else\s+(.*?))?(?:\s*;)?`,
)

var assumeStatementRegex = regexp.MustCompile(
	`(?s)(?:^|\s)assume\s*\((.*?)\)(?:\s+else\s+(.*?))?(?:\s*;)?`,
)

var coverStatementRegex = regexp.MustCompile(
	`(?s)(?:^|\s)cover\s*\((.*?)\)(?:\s*;)?`,
)

// SystemVerilog constraint patterns for randomization constraints
var constraintRegex = regexp.MustCompile(
	`(?s)(?:^|\s)constraint\s+(\w+)\s*\{(.*?)\}`,
)

var constraintBlockRegex = regexp.MustCompile(
	`(?s)(?:^|\s)constraint\s+(\w+)\s*\{(.*?)\}`,
)

// Coverage patterns for coverage constructs
var covergroupRegex = regexp.MustCompile(
	`(?s)(?:^|\s)covergroup\s+(\w+)(?:\s*@\s*\((.*?)\))?\s*;\s+(.*?)\s+endgroup`,
)

var coverpointRegex = regexp.MustCompile(
	`(?s)(?:^|\s)(\w+)\s*:\s*coverpoint\s+(.*?)(?:\s*\{(.*?)\})?(?:\s*;)?`,
)

var crossCoverageRegex = regexp.MustCompile(
	`(?s)(?:^|\s)(\w+)\s*:\s*cross\s+(.*?)(?:\s*\{(.*?)\})?(?:\s*;)?`,
)

// Bind statement patterns
var bindStatementRegex = regexp.MustCompile(
	`(?s)(?:^|\s)bind\s+(\w+)(?:\s*\.\s*(\w+))?\s+(\w+)\s+(\w+)\s*\((.*?)\)\s*;`,
)

var bindModuleRegex = regexp.MustCompile(
	`(?s)(?:^|\s)bind\s+(\w+)\s+(\w+)\s+(\w+)\s*(?:\s*#\s*\((.*?)\))?\s*\((.*?)\)\s*;`,
)

// DPI import/export patterns
var dpiImportRegex = regexp.MustCompile(
	`(?s)(?:^|\s)import\s+"DPI(?:-C)?"\s+(?:context\s+)?(?:pure\s+)?function\s+(\w+)\s+(\w+)\s*\((.*?)\)\s*;`,
)

var dpiExportRegex = regexp.MustCompile(
	`(?s)(?:^|\s)export\s+"DPI(?:-C)?"\s+(?:context\s+)?(?:pure\s+)?function\s+(\w+)\s*;`,
)

var dpiTaskImportRegex = regexp.MustCompile(
	`(?s)(?:^|\s)import\s+"DPI(?:-C)?"\s+(?:context\s+)?task\s+(\w+)\s*\((.*?)\)\s*;`,
)

var dpiTaskExportRegex = regexp.MustCompile(
	`(?s)(?:^|\s)export\s+"DPI(?:-C)?"\s+(?:context\s+)?task\s+(\w+)\s*;`,
)

// Property and sequence patterns
var propertyRegex = regexp.MustCompile(
	`(?s)(?:^|\s)property\s+(\w+)(?:\s*\((.*?)\))?\s*;\s+(.*?)\s+endproperty`,
)

var sequenceRegex = regexp.MustCompile(
	`(?s)(?:^|\s)sequence\s+(\w+)(?:\s*\((.*?)\))?\s*;\s+(.*?)\s+endsequence`,
)

var propertyExprRegex = regexp.MustCompile(
	`(?s)@\s*\((.*?)\)\s+(.*?)(?:\s+disable\s+iff\s*\((.*?)\))?`,
)

// Pragma patterns for synthesis directives
var pragmaRegex = regexp.MustCompile(
	`(?s)\(\*\s*(.*?)\s*\*\)`,
)

var pragmaAttributeRegex = regexp.MustCompile(
	`(?s)\(\*\s*(\w+)(?:\s*=\s*(.*?))?\s*\*\)`,
)

var synthesisRegex = regexp.MustCompile(
	`(?s)(?:^|\s)//\s*(?:synthesis|synopsys)\s+(.*?)$`,
)

var translateOffRegex = regexp.MustCompile(
	`(?m)^\s*//\s*(?:synthesis|synopsys)\s+translate_off\s*$`,
)

var translateOnRegex = regexp.MustCompile(
	`(?m)^\s*//\s*(?:synthesis|synopsys)\s+translate_on\s*$`,
)

// Additional SystemVerilog-specific patterns
var packageImportRegex = regexp.MustCompile( //nolint: unused
	`(?s)(?:^|\s)import\s+(\w+)::(\w+|\*)(?:\s*,\s*(\w+)::(\w+|\*))*\s*;`,
)

var typedefEnumRegex = regexp.MustCompile(
	`(?s)(?:^|\s)typedef\s+enum\s+(?:(\w+)\s+)?\{(.*?)\}\s+(\w+)\s*;`,
)

var typedefStructRegex = regexp.MustCompile(
	`(?s)(?:^|\s)typedef\s+struct\s+(?:packed\s+)?(?:signed\s+)?(?:unsigned\s+)?\{(.*?)\}\s+(\w+)\s*;`,
)

var typedefUnionRegex = regexp.MustCompile(
	`(?s)(?:^|\s)typedef\s+union\s+(?:packed\s+)?(?:tagged\s+)?\{(.*?)\}\s+(\w+)\s*;`,
)

var interfaceInstanceRegex = regexp.MustCompile(
	`(?s)(?:^|\s)(\w+)(?:\s*#\s*\((.*?)\))?\s+(\w+)\s*\((.*?)\)\s*;`,
)

var clockingBlockRegex = regexp.MustCompile(
	`(?s)(?:^|\s)clocking\s+(\w+)\s*@\s*\((.*?)\)\s*;\s+(.*?)\s+endclocking`,
)

var programBlockRegex = regexp.MustCompile(
	`(?s)(?:^|\s)program\s+(\w+)(?:\s*\((.*?)\))?\s*;\s+(.*?)\s+endprogram`,
)

// ===============================================
// Advanced SystemVerilog Construct Matching Functions
// ===============================================

// Generate block matching functions
func matchGenerateBlocksFromString(content string) [][]string {
	return generateBlockRegex.FindAllStringSubmatch(content, -1)
}

func matchGenerateIfsFromString(content string) [][]string {
	return generateIfRegex.FindAllStringSubmatch(content, -1)
}

func matchGenerateForsFromString(content string) [][]string {
	return generateForRegex.FindAllStringSubmatch(content, -1)
}

func matchGenerateCasesFromString(content string) [][]string {
	return generateCaseRegex.FindAllStringSubmatch(content, -1)
}

// Always block matching functions
func matchAlwaysBlocksFromString(content string) [][]string {
	return alwaysBlockRegex.FindAllStringSubmatch(content, -1)
}

func matchAlwaysCombFromString(content string) [][]string {
	return alwaysCombRegex.FindAllStringSubmatch(content, -1)
}

func matchAlwaysFFFromString(content string) [][]string {
	return alwaysFFRegex.FindAllStringSubmatch(content, -1)
}

func matchAlwaysLatchFromString(content string) [][]string {
	return alwaysLatchRegex.FindAllStringSubmatch(content, -1)
}

// Assertion matching functions
func matchAssertPropertiesFromString(content string) [][]string {
	return assertPropertyRegex.FindAllStringSubmatch(content, -1)
}

func matchAssumePropertiesFromString(content string) [][]string {
	return assumePropertyRegex.FindAllStringSubmatch(content, -1)
}

func matchCoverPropertiesFromString(content string) [][]string {
	return coverPropertyRegex.FindAllStringSubmatch(content, -1)
}

func matchRestrictPropertiesFromString(content string) [][]string {
	return restrictPropertyRegex.FindAllStringSubmatch(content, -1)
}

func matchAssertStatementsFromString(content string) [][]string {
	return assertStatementRegex.FindAllStringSubmatch(content, -1)
}

func matchAssumeStatementsFromString(content string) [][]string {
	return assumeStatementRegex.FindAllStringSubmatch(content, -1)
}

func matchCoverStatementsFromString(content string) [][]string {
	return coverStatementRegex.FindAllStringSubmatch(content, -1)
}

// Interface modport matching functions
func matchModportsFromString(content string) [][]string {
	return verilog.ModportRegex.FindAllStringSubmatch(content, -1)
}

func matchModportPortsFromString(content string) [][]string {
	return verilog.ModportPortRegex.FindAllStringSubmatch(content, -1)
}

// Constraint matching functions
func matchConstraintsFromString(content string) [][]string {
	return constraintRegex.FindAllStringSubmatch(content, -1)
}

func matchConstraintBlocksFromString(content string) [][]string {
	return constraintBlockRegex.FindAllStringSubmatch(content, -1)
}

// Coverage matching functions
func matchCovergroupsFromString(content string) [][]string {
	return covergroupRegex.FindAllStringSubmatch(content, -1)
}

func matchCoverpointsFromString(content string) [][]string {
	return coverpointRegex.FindAllStringSubmatch(content, -1)
}

func matchCrossCoverageFromString(content string) [][]string {
	return crossCoverageRegex.FindAllStringSubmatch(content, -1)
}

// Bind statement matching functions
func matchBindStatementsFromString(content string) [][]string {
	return bindStatementRegex.FindAllStringSubmatch(content, -1)
}

func matchBindModulesFromString(content string) [][]string {
	return bindModuleRegex.FindAllStringSubmatch(content, -1)
}

// DPI matching functions
func matchDPIImportsFromString(content string) [][]string {
	return dpiImportRegex.FindAllStringSubmatch(content, -1)
}

func matchDPIExportsFromString(content string) [][]string {
	return dpiExportRegex.FindAllStringSubmatch(content, -1)
}

func matchDPITaskImportsFromString(content string) [][]string {
	return dpiTaskImportRegex.FindAllStringSubmatch(content, -1)
}

func matchDPITaskExportsFromString(content string) [][]string {
	return dpiTaskExportRegex.FindAllStringSubmatch(content, -1)
}

// Property and sequence matching functions
func matchPropertiesFromString(content string) [][]string {
	return propertyRegex.FindAllStringSubmatch(content, -1)
}

func matchSequencesFromString(content string) [][]string {
	return sequenceRegex.FindAllStringSubmatch(content, -1)
}

func matchPropertyExpressionsFromString(content string) [][]string {
	return propertyExprRegex.FindAllStringSubmatch(content, -1)
}

// Pragma matching functions
func matchPragmasFromString(content string) [][]string {
	return pragmaRegex.FindAllStringSubmatch(content, -1)
}

func matchPragmaAttributesFromString(content string) [][]string {
	return pragmaAttributeRegex.FindAllStringSubmatch(content, -1)
}

func matchSynthesisDirectivesFromString(content string) [][]string {
	return synthesisRegex.FindAllStringSubmatch(content, -1)
}

func matchTranslateOffFromString(content string) [][]string {
	return translateOffRegex.FindAllStringSubmatch(content, -1)
}

func matchTranslateOnFromString(content string) [][]string {
	return translateOnRegex.FindAllStringSubmatch(content, -1)
}

// Additional SystemVerilog matching functions
func matchTypedefEnumsFromString(content string) [][]string {
	return typedefEnumRegex.FindAllStringSubmatch(content, -1)
}

func matchTypedefStructsFromString(content string) [][]string {
	return typedefStructRegex.FindAllStringSubmatch(content, -1)
}

func matchTypedefUnionsFromString(content string) [][]string {
	return typedefUnionRegex.FindAllStringSubmatch(content, -1)
}

func matchInterfaceInstancesFromString(content string) [][]string {
	return interfaceInstanceRegex.FindAllStringSubmatch(content, -1)
}

func matchClockingBlocksFromString(content string) [][]string {
	return clockingBlockRegex.FindAllStringSubmatch(content, -1)
}

func matchProgramBlocksFromString(content string) [][]string {
	return programBlockRegex.FindAllStringSubmatch(content, -1)
}

// ===============================================
// End of Advanced SystemVerilog Matching Functions
// ===============================================

// ===============================================
// Test Functions for Advanced SystemVerilog Constructs
// ===============================================

// TestAdvancedSystemVerilogPatterns validates the new regex patterns
func TestAdvancedSystemVerilogPatterns() {
	// This function can be used to test the patterns manually
	// Individual test functions are provided for automated testing
}

// Helper function to test SystemVerilog assertion patterns
func TestAssertionPatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["assert_properties"] = matchAssertPropertiesFromString(content)
	results["assume_properties"] = matchAssumePropertiesFromString(content)
	results["cover_properties"] = matchCoverPropertiesFromString(content)
	results["restrict_properties"] = matchRestrictPropertiesFromString(content)
	results["assert_statements"] = matchAssertStatementsFromString(content)
	results["assume_statements"] = matchAssumeStatementsFromString(content)
	results["cover_statements"] = matchCoverStatementsFromString(content)
	return results
}

// Helper function to test SystemVerilog always block patterns
func TestAlwaysBlockPatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["always_blocks"] = matchAlwaysBlocksFromString(content)
	results["always_comb"] = matchAlwaysCombFromString(content)
	results["always_ff"] = matchAlwaysFFFromString(content)
	results["always_latch"] = matchAlwaysLatchFromString(content)
	return results
}

// Helper function to test SystemVerilog generate patterns
func TestGeneratePatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["generate_blocks"] = matchGenerateBlocksFromString(content)
	results["generate_ifs"] = matchGenerateIfsFromString(content)
	results["generate_fors"] = matchGenerateForsFromString(content)
	results["generate_cases"] = matchGenerateCasesFromString(content)
	return results
}

// Helper function to test SystemVerilog interface patterns
func TestInterfacePatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["modports"] = matchModportsFromString(content)
	results["modport_ports"] = matchModportPortsFromString(content)
	results["interface_instances"] = matchInterfaceInstancesFromString(content)
	return results
}

// Helper function to test SystemVerilog coverage patterns
func TestCoveragePatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["covergroups"] = matchCovergroupsFromString(content)
	results["coverpoints"] = matchCoverpointsFromString(content)
	results["cross_coverage"] = matchCrossCoverageFromString(content)
	return results
}

// Helper function to test SystemVerilog DPI patterns
func TestDPIPatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["dpi_imports"] = matchDPIImportsFromString(content)
	results["dpi_exports"] = matchDPIExportsFromString(content)
	results["dpi_task_imports"] = matchDPITaskImportsFromString(content)
	results["dpi_task_exports"] = matchDPITaskExportsFromString(content)
	return results
}

// Helper function to test SystemVerilog property and sequence patterns
func TestPropertySequencePatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["properties"] = matchPropertiesFromString(content)
	results["sequences"] = matchSequencesFromString(content)
	results["property_expressions"] = matchPropertyExpressionsFromString(content)
	return results
}

// Helper function to test SystemVerilog pragma patterns
func TestPragmaPatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["pragmas"] = matchPragmasFromString(content)
	results["pragma_attributes"] = matchPragmaAttributesFromString(content)
	results["synthesis_directives"] = matchSynthesisDirectivesFromString(content)
	results["translate_off"] = matchTranslateOffFromString(content)
	results["translate_on"] = matchTranslateOnFromString(content)
	return results
}

// Helper function to test other SystemVerilog patterns
func TestOtherSystemVerilogPatterns(content string) map[string][][]string {
	results := make(map[string][][]string)
	results["typedef_enums"] = matchTypedefEnumsFromString(content)
	results["typedef_structs"] = matchTypedefStructsFromString(content)
	results["typedef_unions"] = matchTypedefUnionsFromString(content)
	results["constraints"] = matchConstraintsFromString(content)
	results["bind_statements"] = matchBindStatementsFromString(content)
	results["bind_modules"] = matchBindModulesFromString(content)
	results["clocking_blocks"] = matchClockingBlocksFromString(content)
	results["program_blocks"] = matchProgramBlocksFromString(content)
	return results
}

// ===============================================
// End of Test Functions for Advanced SystemVerilog Constructs
// ===============================================
