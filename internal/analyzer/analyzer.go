package analyzer

import (
	"fmt"
	"log"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// EnumCast represents a detected enum cast in SystemVerilog
type EnumCast struct {
	Line       string
	EnumType   string
	Expression string
	DefaultVal string
}

// UndefinedIdentifier represents a detected undefined identifier
type UndefinedIdentifier struct {
	Line    string
	Name    string
	Context string
}

// AnalyzeVerilogFile analyzes a SystemVerilog file and returns processed content
func AnalyzeVerilogFile(filepath string) (string, error) {
	content, err := utils.ReadFileContent(filepath)
	if err != nil {
		return "", fmt.Errorf("failed to read verilog file: %v", err)
	}

	// Remove comments from the content
	content = utils.RemoveComments(content)

	// Remove unique from case statements
	content = utils.RemoveUniqueCases(content)

	// First, find all existing package definitions in the content
	definedPackages := findExistingPackages(content)

	// Extract enum types for later processing
	enums := ExtractEnumTypes(content)
	if len(enums) > 0 {
		log.Println("Detected enum types that will be mocked:")
		for _, enum := range enums {
			log.Printf("  %s::%s with %d values\n", enum.Package, enum.Name, len(enum.Values))
		}

		// Filter out enums from packages that are already defined
		var newEnums []EnumDefinition
		for _, enum := range enums {
			if !definedPackages[enum.Package] {
				newEnums = append(newEnums, enum)
			} else {
				log.Printf("Skipping enum from already defined package: %s::%s",
					enum.Package, enum.Name)
			}
		}

		// Generate enum definitions only for packages that aren't defined already
		if len(newEnums) > 0 {
			enumDefs := GenerateEnumDefinitions(newEnums)

			// Add Verilator lint pragma to disable width warnings at the top of the file
			if !strings.Contains(content, "verilator lint_off WIDTHEXPAND") {
				content = "/* verilator lint_off WIDTHEXPAND */\n" + content
			}

			// Insert the enum definitions before the module declaration
			modulePos := strings.Index(content, "module ")
			if modulePos > 0 {
				content = content[:modulePos] + enumDefs + content[modulePos:]
			}
		}

		// Make port declarations more explicit by adding package qualification
		// This helps prevent name collisions with enum values
		for _, enum := range enums {
			portRegex := regexp.MustCompile(fmt.Sprintf(`(input|output|inout)\\s+(%s)\\s+(\\w+)`,
				regexp.QuoteMeta(enum.Name)))
			content = portRegex.ReplaceAllString(content,
				fmt.Sprintf("$1 %s::$2 $3", enum.Package))
		}

		// Insert import statements inside the module for ALL enum packages
		// (even defined ones need to be imported)
		modulePos := strings.Index(content, "module ")
		moduleHeaderEnd := strings.Index(content[modulePos:], ");")
		if modulePos > 0 && moduleHeaderEnd > 0 {
			moduleHeaderEnd += modulePos + 2 // +2 for ");"

			// Generate the import statements for all the packages
			var importStmt strings.Builder
			importStmt.WriteString("\n  // Import statements for enum packages\n")

			// Track packages to avoid duplicates
			importedPackages := make(map[string]bool)

			for _, enum := range enums {
				if !importedPackages[enum.Package] {
					importStmt.WriteString(fmt.Sprintf("  import %s::*;\n", enum.Package))
					importedPackages[enum.Package] = true
				}
			}

			// Insert imports after the module header
			content = content[:moduleHeaderEnd] + importStmt.String() + content[moduleHeaderEnd:]
		}
	}

	// Fix module port declarations for enums (add package qualification to output params)
	content = fixModulePortsForEnums(content, enums)

	// Detect and remove macros
	macros := DetectMacros(content)
	if len(macros) > 0 {
		log.Println("Detected macros that will be removed:")
		for _, macro := range macros {
			log.Printf("  %s\n", macro)
		}
		content = RemoveMacros(content, macros)
	}

	// Detect enum casts
	enumCasts := DetectEnumCasts(filepath)
	if len(enumCasts) > 0 {
		log.Println("Detected enum casts and their mocked values:")
		for _, cast := range enumCasts {
			log.Printf("  Type: %s, Expression: %s -> Mocked: %s\n",
				cast.EnumType, cast.Expression, cast.EnumType)
		}
		// We don't replace the casts anymore - we keep them intact
		// The import statements will ensure the enum types are available
	}

	// Detect undefined identifiers (handle these after enum processing)
	undefinedVars := DetectUndefinedIdentifiers(filepath)
	if len(undefinedVars) > 0 {
		log.Println("Detected undefined identifiers and their mocked values:")
		for _, undef := range undefinedVars {
			mockedValue := MockIdentifier(undef)
			log.Printf("  Name: %s, Context: %s -> Mocked: %s\n",
				undef.Name, undef.Context, mockedValue)
		}

		for _, undef := range undefinedVars {
			// Only mock certain types of identifiers, and avoid ones that will be handled by our enum system
			if !strings.Contains(undef.Name, "::") &&
				!isEnumIdentifier(undef.Name, enums) &&
				(strings.HasSuffix(undef.Name, "_e") ||
					strings.HasSuffix(undef.Name, "_t") ||
					strings.Contains(undef.Context, "parameter")) {
				content = strings.Replace(content, undef.Name,
					MockIdentifier(undef), -1)
			}
		}
	}

	// Rename the module
	moduleRegex := regexp.MustCompile(`module\s+(\w+)\s*(\#\s*\([^)]*\))?\s*\(`)
	content = moduleRegex.ReplaceAllString(content, "module ${1}_mocked${2} (")

	return content, nil
}

// isEnumIdentifier checks if a name is already defined in our enum definitions
func isEnumIdentifier(name string, enums []EnumDefinition) bool {
	for _, enum := range enums {
		if enum.Name == name {
			return true
		}

		// Also check enum values
		for _, val := range enum.Values {
			if val == name {
				return true
			}
		}
	}
	return false
}

// Helper function to check if content already has package definitions for our enums
func containsDuplicatePackages(content string, enums []EnumDefinition) bool {
	for _, enum := range enums {
		// Look for package definitions like "package ibex_pkg;"
		packagePattern := fmt.Sprintf("package\\s+%s\\s*;", enum.Package)
		packageRegex := regexp.MustCompile(packagePattern)
		if packageRegex.MatchString(content) {
			return true
		}
	}
	return false
}

// findExistingPackages returns a map of package names that are already defined in the content
func findExistingPackages(content string) map[string]bool {
	packages := make(map[string]bool)

	packageRegex := regexp.MustCompile(`package\s+(\w+)\s*;`)
	matches := packageRegex.FindAllStringSubmatch(content, -1)

	for _, match := range matches {
		if len(match) >= 2 {
			pkgName := match[1]
			packages[pkgName] = true
			log.Printf("Found existing package definition: %s", pkgName)
		}
	}

	return packages
}

// fixModulePortsForEnums adds package qualification to enum ports to avoid name conflicts
func fixModulePortsForEnums(content string, enums []EnumDefinition) string {
	moduleRegex := regexp.MustCompile(`(module\s+\w+_mocked\s*\()([^)]*)\)`)

	return moduleRegex.ReplaceAllStringFunc(content, func(match string) string {
		matches := moduleRegex.FindStringSubmatch(match)
		if len(matches) < 3 {
			return match
		}

		moduleHeader := matches[1]
		portList := matches[2]

		// Process each port in the port list
		for _, enum := range enums {
			enumRegex := regexp.MustCompile(fmt.Sprintf(`(output|input|inout)\s+(%s)\s+(\w+)`,
				regexp.QuoteMeta(enum.Name)))
			portList = enumRegex.ReplaceAllString(portList,
				fmt.Sprintf("$1 %s::$2 $3", enum.Package))
		}

		return moduleHeader + portList + ")"
	})
}
