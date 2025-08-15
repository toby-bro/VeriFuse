package mutate

import (
	"fmt"
	"math/rand"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
	"golang.org/x/exp/maps"
)

var logger *utils.DebugLogger

func loadLogger(v int) {
	if logger == nil {
		logger = utils.NewDebugLogger(v)
	}
}

func injectSnippetInModule(
	targetModule *verilog.Module,
	targetFile *verilog.VerilogFile,
	snippet *snippets.Snippet,
	instantiate bool,
	workerDir string,
) error {
	scopeTree, err := verilog.GetScopeTree(
		targetFile,
		targetModule.Body,
		targetModule.Parameters,
		targetModule.Ports,
	)
	if err != nil {
		return fmt.Errorf("[%s] failed to extract variables from module: %v", workerDir, err)
	}
	if scopeTree == nil {
		return fmt.Errorf(
			"[%s] failed to parse scope tree for module %s",
			workerDir,
			targetModule.Name,
		)
	}

	bestScope := findBestScopeNode(scopeTree)
	if bestScope == nil {
		logger.Warn(
			"[%s] Could not determine a best scope for snippet %s in module %s. Using module root.",
			workerDir,
			snippet.Name,
			targetModule.Name,
		)
		bestScope = scopeTree
	}

	logger.Info(
		"[%s] Best scope for snippet %s in module %s is at level %d with %d accessible variables",
		workerDir,
		snippet.Name,
		targetModule.Name,
		bestScope.Level,
		len(bestScope.Variables),
	)
	logger.Debug("[%s] Scope tree for module %s:\n%s",
		workerDir,
		targetModule.Name,
		bestScope.Dump(1),
	)

	portConnections, newSignalDeclarations, err := matchVariablesToSnippetPorts(
		targetModule,
		snippet,
		workerDir,
		bestScope,
	)
	if err != nil {
		return fmt.Errorf("failed to match variables to snippet ports: %v", err)
	}

	logger.Debug(
		"[%s] Matched ports for snippet %s in module %s: %v",
		workerDir,
		snippet.Name,
		targetModule.Name,
		portConnections,
	)

	err = ensureOutputPortForSnippet(targetModule, snippet, portConnections)
	if err != nil {
		return fmt.Errorf("failed to ensure output port for snippet: %v", err)
	}

	var injection string
	if instantiate {
		injection = generateSnippetInstantiation(snippet, portConnections)
	} else {
		injection = generateSnippetInjection(snippet, portConnections)
		targetModule.Parameters = append(targetModule.Parameters, snippet.Module.Parameters...)
	}

	err = injectSnippetIntoModule(
		targetModule,
		injection,
		newSignalDeclarations,
		bestScope,
		workerDir,
	)
	if err != nil {
		return fmt.Errorf("failed to insert snippet into module: %v", err)
	}
	if instantiate {
		logger.Info(
			"[%s] Instantiated snippet %s into module %s at scope level %d",
			workerDir,
			snippet.Name,
			targetModule.Name,
			bestScope.Level,
		)
	} else {
		logger.Info(
			"[%s] Injected snippet %s into module %s at scope level %d",
			workerDir,
			snippet.Name,
			targetModule.Name,
			bestScope.Level,
		)
	}

	return nil
}

func matchVariablesToSnippetPorts(
	module *verilog.Module,
	snippet *snippets.Snippet,
	debugWorkerDir string,
	bestScopeForSnippet *verilog.ScopeNode,
) (map[string]string, []*verilog.Port, error) {
	portConnections := make(map[string]string)
	newDeclarations := []*verilog.Port{}

	usedInternalVars := make(map[string]bool)
	usedModuleInputPorts := make(map[string]bool)
	// Tracks module variable names (from scope or module ports) already connected to a snippet port
	overallAssignedModuleVarNames := make(map[string]bool)
	clockPorts, resetPorts, _ := verilog.IdentifyClockAndResetPorts(snippet.Module)
	ogClockPort := verilog.GetClockPort(module)
	if ogClockPort == nil {
		ogClockPort = &verilog.Port{
			Name:      "clk",
			Direction: verilog.INPUT,
			Type:      verilog.WIRE,
			IsSigned:  false,
		}
		module.Ports = append(module.Ports, ogClockPort)
		logger.Debug(
			"[%s] No clock port found in module %s, created default clock port %s",
			debugWorkerDir,
			module.Name,
			ogClockPort.Name,
		)
		if !module.AnsiStyle {
			signal := generateSignalDeclaration(ogClockPort, ogClockPort.Name)
			if err := insertTextAtLine(
				module,
				signal,
				0,
				1,
			); err != nil {
				logger.Error("failed to insert clock port signal declaration: %v", err)
			}
		}
	}
	ogResetPort := verilog.GetResetPort(module)
	if ogResetPort == nil {
		ogResetPort = &verilog.Port{
			Name:      "rst",
			Direction: verilog.INPUT,
			Type:      verilog.WIRE,
			IsSigned:  false,
		}
		module.Ports = append(module.Ports, ogResetPort)
		logger.Debug(
			"[%s] No reset port found in module %s, created default reset port %s",
			debugWorkerDir,
			module.Name,
			ogResetPort.Name,
		)
		if !module.AnsiStyle {
			signal := generateSignalDeclaration(ogResetPort, ogResetPort.Name)
			if err := insertTextAtLine(
				module,
				signal,
				0,
				1,
			); err != nil {
				logger.Error("failed to insert reset port signal declaration: %v", err)
			}
		}
	}

	for _, port := range snippet.Module.Ports {
		foundMatch := false
		var connectedVarName string
		switch {
		case slices.Contains(clockPorts, port):
			connectedVarName = ogClockPort.Name
		case slices.Contains(resetPorts, port):
			connectedVarName = ogResetPort.Name
		case len(bestScopeForSnippet.Variables) > 0:
			var varsAccessibleInBestScope map[string]*verilog.Variable
			if port.Direction == verilog.INPUT {
				varsAccessibleInBestScope = collectAccessibleVarsForInput(bestScopeForSnippet)
			} else {
				varsAccessibleInBestScope = make(map[string]*verilog.Variable)
			}

			matchedVarFromScope := findMatchingVariable(
				port,
				varsAccessibleInBestScope,
				usedInternalVars,
			)
			// Check if this variable name has already been assigned to another snippet port
			if matchedVarFromScope != nil &&
				!overallAssignedModuleVarNames[matchedVarFromScope.Name] {
				connectedVarName = matchedVarFromScope.Name
			}
		}
		if connectedVarName != "" {
			portConnections[port.Name] = connectedVarName
			usedInternalVars[connectedVarName] = true              // Mark as used for this strategy
			overallAssignedModuleVarNames[connectedVarName] = true // Mark as globally assigned
			foundMatch = true
		}

		if !foundMatch {
			if port.Direction == verilog.INPUT {
				for _, modulePort := range module.Ports {
					if modulePort.Direction == verilog.INPUT &&
						modulePort.Type == port.Type &&
						modulePort.Width == port.Width &&
						!usedModuleInputPorts[modulePort.Name] && // Ensure this module input port isn't already used by this strategy
						!overallAssignedModuleVarNames[modulePort.Name] { // Ensure this module port name isn't globally assigned
						connectedVarName = modulePort.Name
						portConnections[port.Name] = connectedVarName
						usedModuleInputPorts[connectedVarName] = true          // Mark as used for this strategy
						overallAssignedModuleVarNames[connectedVarName] = true // Mark as globally assigned
						foundMatch = true
						break
					}
				}
			}
			// Note: OUTPUT ports are never matched to existing module output ports
			// They always get new variables created to avoid multiple drivers
		}

		if !foundMatch {
			// Generate timestamp only where we actually need it for renaming
			timestamp := time.Now().UnixNano() / int64(time.Millisecond)
			newSignalName := fmt.Sprintf(
				"inj_%s_%d_%d",
				strings.ToLower(port.Name),
				timestamp,
				rand.Intn(1000),
			)
			newSignalObj := &verilog.Port{
				Name:            newSignalName,
				Type:            port.Type,
				Width:           port.Width,
				IsSigned:        port.IsSigned,
				Direction:       port.Direction,
				AlreadyDeclared: !module.AnsiStyle,
			}
			newDeclarations = append(newDeclarations, newSignalObj)
			portConnections[port.Name] = newSignalName

			logger.Debug(
				"[%s] Created new signal %s for port %s in snippet %s (timestamp %d) and AnsiStyle %t",
				debugWorkerDir,
				newSignalName,
				port.Name,
				snippet.Name,
				timestamp,
				module.AnsiStyle,
			)
			// Newly created signals are unique by generation and don't need to be added to overallAssignedModuleVarNames
		}
	}

	return portConnections, newDeclarations, nil
}

func findBestScopeNode(
	rootNode *verilog.ScopeNode,
) *verilog.ScopeNode {
	if rootNode == nil {
		return nil
	}
	bestScope := rootNode
	maxVariableCount := -1

	var dfs func(currentNode *verilog.ScopeNode, parentAccessibleVars map[string]*verilog.Variable)
	dfs = func(currentNode *verilog.ScopeNode, parentAccessibleVars map[string]*verilog.Variable) {
		currentScopeAndParentVars := make(
			map[string]*verilog.Variable,
		)
		// Copy current node variables from ScopeVariable to Variable map
		for name, scopeVar := range currentNode.Variables {
			currentScopeAndParentVars[name] = scopeVar
		}
		maps.Copy(currentScopeAndParentVars, parentAccessibleVars)

		currentVariableCount := len(currentScopeAndParentVars)

		if currentVariableCount > maxVariableCount {
			maxVariableCount = currentVariableCount
			bestScope = currentNode
		}

		varsForChildren := make(
			map[string]*verilog.Variable,
		)
		// Copy current node variables from ScopeVariable to Variable map
		for name, scopeVar := range currentNode.Variables {
			varsForChildren[name] = scopeVar
		}
		maps.Copy(
			varsForChildren,
			parentAccessibleVars,
		)

		for _, child := range currentNode.Children {
			dfs(child, varsForChildren)
		}
	}

	dfs(rootNode, make(map[string]*verilog.Variable))

	return bestScope
}

// This function collects all accessible variables from the given scope node and its parents.
// It returns a map of variable names to their corresponding Variable objects.
// This is useful for matching snippet ports to existing variables in the module.
func collectAccessibleVarsForInput(node *verilog.ScopeNode) map[string]*verilog.Variable {
	collectedVars := make(map[string]*verilog.Variable)
	curr := node
	for curr != nil {
		for name, scopeVar := range curr.Variables {
			collectedVars[name] = scopeVar
		}
		curr = curr.Parent
	}
	return collectedVars
}

// This function finds a matching variable for a given port in the provided variables map.
func findMatchingVariable(
	port *verilog.Port,
	variables map[string]*verilog.Variable,
	usedVars map[string]bool,
) *verilog.Variable {
	for _, variable := range variables {
		if !usedVars[variable.Name] && variable.Type == port.Type && variable.Width == port.Width {
			return variable
		}
	}
	return nil
}

func generateSignalDeclaration(port *verilog.Port, signalName string) string {
	widthStr := ""
	if port.Width > 1 {
		widthStr = fmt.Sprintf("[%d:0] ", port.Width-1)
	}
	signedStr := ""
	if port.IsSigned {
		signedStr = "signed "
	}
	directionStr := ""
	switch port.Direction {
	case verilog.INPUT:
		directionStr = "input "
	case verilog.OUTPUT:
		directionStr = "output "
	case verilog.INOUT:
		directionStr = "inout "
	case verilog.INTERNAL:
		directionStr = ""
	}

	typeStr := port.Type.String()
	if typeStr == "" {
		typeStr = "logic" // fallback
	}

	return fmt.Sprintf("%s%s %s%s%s;", directionStr, typeStr, signedStr, widthStr, signalName)
}

func ensureOutputPortForSnippet(
	module *verilog.Module,
	snippet *snippets.Snippet,
	portConnections map[string]string,
) error {
	for _, port := range snippet.Module.Ports {
		if port.Direction == verilog.OUTPUT {
			if _, exists := portConnections[port.Name]; !exists {
				newPort := verilog.Port{
					Name:      "inj_output_" + strings.ToLower(port.Name),
					Direction: verilog.OUTPUT,
					Type:      port.Type,
					Width:     port.Width,
					IsSigned:  port.IsSigned,
				}
				module.Ports = append(module.Ports, &newPort)
				portConnections[port.Name] = newPort.Name
			}
		}
	}
	return nil
}

// This function replaces the port names in the snippet string with the corresponding signal names
// from the portConnection map. It returns the modified snippet string.
func replacePortNames(snippetString string, portConnection map[string]string) string {
	for portName, signalName := range portConnection {
		re := regexp.MustCompile(`\b` + regexp.QuoteMeta(portName) + `\b`)
		snippetString = re.ReplaceAllString(snippetString, signalName)
	}
	return snippetString
}

// This function replaces variable names in the snippet string with their timestamped versions
// to avoid naming conflicts when the same snippet is injected multiple times.
func replaceVariableNames(snippetString string, variableRenameMap map[string]string) string {
	for originalName, timestampedName := range variableRenameMap {
		re := regexp.MustCompile(`\b` + regexp.QuoteMeta(originalName) + `\b`)
		snippetString = re.ReplaceAllString(snippetString, timestampedName)
	}
	return snippetString
}

// This function changes the names of the port variables in the snippet to match the names given in portConnections
// It returns a string that can be directly injected into any other module at the given scope level.
func generateSnippetInjection(
	snippet *snippets.Snippet,
	portConnections map[string]string,
) string {
	snippetString := snippet.Module.Body
	snippetString = replacePortNames(snippetString, portConnections)

	// Parse all variables in the snippet body to rename internal variables with timestamp
	snippetVariables, err := verilog.ParseVariables(nil, snippetString, snippet.Module.Parameters)
	if err != nil {
		logger.Debug("Failed to parse variables from snippet %s: %v", snippet.Name, err)
	} else {
		// Generate timestamp for unique variable naming
		timestamp := time.Now().UnixNano() / int64(time.Millisecond)

		// Create a mapping of original variable names to timestamped versions
		variableRenameMap := make(map[string]string)
		for varName := range snippetVariables {
			// Skip ports as they are already handled by portConnections
			isPort := false
			for _, port := range snippet.Module.Ports {
				if port.Name == varName {
					isPort = true
					break
				}
			}
			if !isPort {
				timestampedVarName := fmt.Sprintf("%s_ts%d", varName, timestamp)
				variableRenameMap[varName] = timestampedVarName
			}
		}

		// Replace all internal variable names with timestamped versions
		snippetString = replaceVariableNames(snippetString, variableRenameMap)

		logger.Debug("Renamed %d internal variables in snippet %s with timestamp %d",
			len(variableRenameMap), snippet.Name, timestamp)
	}

	snippetString = utils.TrimEmptyLines(snippetString)

	// Generate timestamp only where we actually need it for unique naming
	timestamp := time.Now().UnixNano() / int64(time.Millisecond)
	snippetIdentifier := fmt.Sprintf("%s_ts%d", strings.TrimSpace(snippet.Name), timestamp)
	snippetString = fmt.Sprintf(
		"    // BEGIN: %s\n%s\n    // END: %s\n",
		snippetIdentifier,
		snippetString,
		snippetIdentifier,
	)

	return snippetString
}

func generateSnippetInstantiation(
	snippet *snippets.Snippet,
	portConnections map[string]string,
) string {
	// Generate timestamp only where we actually need it for unique naming
	timestamp := time.Now().UnixNano() / int64(time.Millisecond)
	instanceName := fmt.Sprintf("%s_inst_%d_%d", snippet.Name, timestamp, rand.Intn(10000))
	instantiation := fmt.Sprintf("%s %s (\n", snippet.Module.Name, instanceName)

	connectionLines := []string{}
	for portName, signalName := range portConnections {
		connectionLines = append(connectionLines, fmt.Sprintf("    .%s(%s)", portName, signalName))
	}
	instantiation += strings.Join(connectionLines, ",\n")
	instantiation += "\n);"

	return utils.Indent(instantiation)
}

func insertTextAtLine(module *verilog.Module, text string, line int, indentLevel int) error {
	lines := strings.Split(module.Body, "\n")
	if line < 0 || line > len(lines) {
		return fmt.Errorf("line number %d is out of bounds for module %s", line, module.Name)
	}

	for range indentLevel {
		text = utils.Indent(text)
	}
	textLines := strings.Split(text, "\n")

	lines = append(lines[:line], append(textLines, lines[line:]...)...)
	module.Body = strings.Join(lines, "\n")

	return nil
}

func injectSnippetIntoModule(
	module *verilog.Module,
	instantiation string,
	newDeclarations []*verilog.Port,
	bestScope *verilog.ScopeNode,
	debugWorkerDir string,
) error {
	// Determine the insertion line based on the best scope's LastLine
	var insertionLine int
	endOfDecls := findEndOfModuleDeclarations(strings.Split(module.Body, "\n"))
	if bestScope != nil && bestScope.LastLine > -1 {
		// Insert after the last line where a variable was declared in this scope
		insertionLine = bestScope.LastLine + 1
		logger.Debug(
			"[%s] Using scope-based insertion at line %d (scope level %d)",
			debugWorkerDir,
			insertionLine,
			bestScope.Level,
		)
	} else {
		// Fallback to the old method
		insertionLine = endOfDecls
		logger.Debug(
			"[%s] Using fallback insertion at line %d (no best scope found)",
			debugWorkerDir,
			insertionLine,
		)
	}

	// Add new signal declarations first (if needed)
	if !module.AnsiStyle {
		for i := len(newDeclarations) - 1; i >= 0; i-- {
			portToDeclare := newDeclarations[i]
			declarationString := generateSignalDeclaration(portToDeclare, portToDeclare.Name)
			err := insertTextAtLine(
				module,
				declarationString,
				endOfDecls,
				1,
			)
			if err != nil {
				return fmt.Errorf("failed to insert signal declaration: %v", err)
			}
			// Increment insertion line for next declaration
			endOfDecls++
		}
	}
	logger.Debug(
		"[%s] Inserted %d new signal declarations at line %d in module %s",
		debugWorkerDir,
		len(newDeclarations),
		insertionLine,
		module.Name,
	)

	// Add the new ports to the module
	module.Ports = append(module.Ports, newDeclarations...)

	// Insert the snippet instantiation/injection
	err := insertTextAtLine(module, instantiation, insertionLine, bestScope.Level)
	if err != nil {
		return fmt.Errorf("failed to insert snippet: %v", err)
	}

	return nil
}

func findEndOfModuleDeclarations(lines []string) int {
	lastDeclarationLine := -1
	for i, line := range lines {
		trimmedLine := strings.TrimSpace(line)

		if strings.HasPrefix(trimmedLine, "//") || trimmedLine == "" {
			continue
		}

		if strings.HasPrefix(trimmedLine, "assign ") ||
			strings.HasPrefix(trimmedLine, "always") ||
			strings.HasPrefix(trimmedLine, "initial ") ||
			strings.HasPrefix(trimmedLine, "generate") ||
			(strings.Contains(trimmedLine, "(") && !isDeclarationLine(trimmedLine) &&
				!strings.HasPrefix(trimmedLine, "function ") &&
				!strings.HasPrefix(trimmedLine, "task ") &&
				!strings.HasPrefix(trimmedLine, "module ")) {
			if lastDeclarationLine != -1 {
				return lastDeclarationLine + 1
			}
			return i
		}

		if isDeclarationLine(trimmedLine) {
			lastDeclarationLine = i
		}

		if strings.HasPrefix(trimmedLine, "endmodule") {
			if lastDeclarationLine != -1 {
				return lastDeclarationLine + 1
			}
			return i
		}
	}

	if lastDeclarationLine != -1 {
		return lastDeclarationLine + 1
	}

	for i := len(lines) - 1; i >= 0; i-- {
		if strings.Contains(lines[i], "endmodule") {
			return i
		}
	}
	return len(lines)
}

func isDeclarationLine(line string) bool {
	trimmedLine := strings.TrimSpace(line)
	declarationKeywords := []string{
		"input", "output", "inout", "reg", "wire", "logic", "integer", "real", "time", "realtime",
		"bit", "byte", "shortint", "int", "longint", "shortreal", "string", "parameter", "localparam",
		"genvar", "typedef", "struct", "enum", "class",
	}
	for _, keyword := range declarationKeywords {
		if strings.HasPrefix(trimmedLine, keyword+" ") ||
			strings.HasPrefix(trimmedLine, keyword+"[") {
			return true
		}
	}
	if !strings.Contains(trimmedLine, "(") && strings.HasSuffix(trimmedLine, ";") &&
		strings.Count(trimmedLine, " ") >= 1 {
		if !strings.ContainsAny(strings.Split(trimmedLine, " ")[0], "=+-*/%&|^<>()[]{}:;") {
			return true
		}
	}
	return false
}

var maxSnippets float64 = 20

func Gx() float32 {
	x := rand.Float64()
	return float32((1-1/maxSnippets-x)*(1-1/maxSnippets-x)*(1-1/maxSnippets-x) + 1/maxSnippets)
}

var target float32 = 0.75

// MutateFile applies mutations to the given Verilog file by injecting random snippets into its modules.
func MutateFile( //nolint: revive
	svFile *verilog.VerilogFile,
	g float32,
	workerDir string,
	verbose int,
) bool {
	if g == 0 {
		g = Gx()
	}
	loadLogger(verbose)
	fileName := svFile.Name
	mutatedOverall := false
	for {
		for moduleName, currentModule := range svFile.Modules {
			if len(svFile.DependencyMap[moduleName].DependedBy) > 0 {
				logger.Debug(
					"[%s] Skipping module %s due to dependencies: %v",
					workerDir,
					moduleName,
					svFile.DependencyMap[moduleName].DependedBy,
				)
				continue
			}

			moduleToMutate := currentModule.DeepCopy()
			if moduleToMutate == nil {
				logger.Warn(
					"[%s] Failed to copy module %s for mutation, skipping.",
					workerDir,
					moduleName,
				)
				continue
			}

			snippet, err := snippets.GetRandomSnippet(verbose, g, target)
			if err != nil {
				logger.Warn(
					"[%s] Failed to get snippet for module %s: %v. Skipping mutation for this module.",
					workerDir,
					moduleName,
					err,
				)
				continue
			}
			if snippet == nil || snippet.Module == nil || snippet.ParentFile == nil {
				logger.Warn(
					"[%s] Selected snippet, its module, or its parent file is nil for module %s. Skipping.",
					workerDir,
					moduleName,
				)
				continue
			}
			if snippet.ParentFile.Name == "" {
				logger.Warn(
					"[%s] Snippet ParentFile name is empty for snippet '%s'. Dependency merging might be affected.",
					workerDir,
					snippet.Name,
				)
			}

			logger.Debug(
				"[%s] Attempting to inject snippet %s in module %s from file %s...",
				workerDir,
				snippet.Name,
				moduleToMutate.Name,
				fileName,
			)
			instantiate := rand.Intn(3) == 0
			err = injectSnippetInModule(
				moduleToMutate,
				svFile,
				snippet,
				instantiate,
				workerDir,
			)
			if err != nil {
				logger.Info(
					"[%s] InjectSnippet failed for module %s: %v. Skipping mutation for this module.",
					workerDir,
					moduleToMutate.Name,
					err,
				)
				continue
			}

			svFile.Modules[moduleName] = moduleToMutate

			err = snippets.GeneralAddDependencies(svFile, snippet, instantiate)
			if err != nil {
				logger.Error(
					"[%s] Failed to add dependencies for snippet %s: %v. Continuing with mutation.",
					workerDir,
					snippet.Name,
					err,
				)
			}

			logger.Debug(
				"[%s] Successfully injected snippet %s into module %s with timestamped variables",
				workerDir,
				snippet.Name,
				moduleToMutate.Name,
			)

			if instantiate {
				svFile.AddDependency(
					moduleToMutate.Name,
					snippet.Module.Name,
				)
			} else {
				svFile.AddDependency(
					moduleToMutate.Name,
					snippet.ParentFile.DependencyMap[snippet.Name].DependsOn...,
				)
			}

			mutatedOverall = true
			logger.Debug(
				"[%s] Mutation applied to module %s in %s",
				workerDir,
				moduleToMutate.Name,
				fileName,
			)
		}
		if rand.Float32() < g {
			break
		}
	}
	return mutatedOverall
}

// MutateAndRewriteFile applies mutations to the given Verilog file and writes the mutated content to the specified path.
func MutateAndRewriteFile( //nolint: revive
	originalSvFile *verilog.VerilogFile,
	pathToWrite string,
	verbose int,
) (*verilog.VerilogFile, error) {
	svFile := originalSvFile.DeepCopy()
	loadLogger(verbose)

	workerDir := filepath.Base(filepath.Dir(pathToWrite))
	g := Gx()
	mutatedOverall := MutateFile(svFile, g, workerDir, verbose)

	if !mutatedOverall {
		logger.Info(
			"[%s] No successful mutations applied to file %s. Writing original or partially modified content if other steps occurred.",
			workerDir,
			pathToWrite,
		)
	}

	finalMutatedContent, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return nil, fmt.Errorf(
			"[%s] failed to print Verilog file %s after mutation: %v",
			workerDir,
			pathToWrite,
			err,
		)
	}
	err = utils.WriteFileContent(pathToWrite, finalMutatedContent)
	if err != nil {
		return nil, fmt.Errorf("failed to write mutated content to %s: %v", pathToWrite, err)
	}

	if mutatedOverall {
		logger.Debug("[%s] Successfully mutated and rewrote file %s", workerDir, pathToWrite)
	} else {
		logger.Warn("[%s] File %s rewritten (no mutations applied or all failed).", workerDir, pathToWrite)
	}

	return svFile, nil
}
