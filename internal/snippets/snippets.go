package snippets

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// SnippetScore represents the performance metrics for a snippet
type SnippetScore struct {
	NumSimulators    int     // number of simulators (without their synthesized derivatives)
	NumSynthesizers  int     // number of synthesizers
	SimulatorScore   int     // achieved simulator score
	SynthesizerScore int     // achieved synthesizer score
	MaximalScore     int     // maximal possible score (2*simulators + synthesizers)
	ReachedScore     int     // actual reached score
	Probability      float64 // calculated probability (reachedScore/maximalScore)
}

type Snippet struct {
	Name       string
	Module     *verilog.Module
	ParentFile *verilog.VerilogFile
	Score      *SnippetScore // nil if no score file exists
}

var (
	snippets     = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}
	logger       = *utils.NewDebugLogger(1)
	loadOnce     sync.Once
	loadError    error
)

func findSnippetFiles() ([]string, error) {
	repoRoot, err := utils.GetRootDir()
	if err != nil || repoRoot == "" {
		return nil, fmt.Errorf("failed to find repository root: %w", err)
	}

	snippetsDir := filepath.Join(repoRoot, "isolated")

	if _, err := os.Stat(snippetsDir); os.IsNotExist(err) {
		return nil, fmt.Errorf("snippets directory '%s' does not exist", snippetsDir)
	} else if err != nil {
		return nil, fmt.Errorf("failed to access snippets directory '%s': %w", snippetsDir, err)
	}

	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "**/*.sv"))
	logger.Debug("Loading snippets from directory: %s", snippetsDir)
	if err != nil {
		return nil, err
	}
	return sourceFiles, nil
}

// FindSnippetFiles returns all snippet files in the isolated directory
func FindSnippetFiles() ([]string, error) {
	return findSnippetFiles()
}

func loadSnippets() error {
	sourceFiles, err := findSnippetFiles()
	if err != nil {
		return fmt.Errorf("failed to find snippet files: %v", err)
	}
	for _, snippetFile := range sourceFiles {
		fileContent, err := utils.ReadFileContent(snippetFile)
		if err != nil {
			return fmt.Errorf("failed to read snippet file %s: %v", snippetFile, err)
		}
		verilogFile, err := verilog.ParseVerilog(fileContent, logger.GetVerboseLevel())
		verilogFile.Name = snippetFile
		if err != nil || verilogFile == nil {
			return err
		}
		for _, module := range verilogFile.Modules {
			if module.Name == "" {
				return fmt.Errorf("module name is empty in file %s", snippetFile)
			}
			if module.Name == "top" {
				module.Name = "topi"
			}

			// Try to load score file for this snippet
			score, err := loadScoreFile(snippetFile, module.Name)
			if err != nil {
				logger.Debug("No score file found for snippet %s: %v", module.Name, err)
			}

			snippets = append(snippets, &Snippet{
				Name:       module.Name,
				Module:     module,
				ParentFile: verilogFile,
				Score:      score,
			})
			verilogFiles = append(verilogFiles, verilogFile)
		}
	}
	logger.Debug("Loaded %d snippets from %d files", len(snippets), len(sourceFiles))
	return nil
}

func getSnippets() ([]*Snippet, []*verilog.VerilogFile, error) {
	loadOnce.Do(func() {
		loadError = loadSnippets()
	})
	if loadError != nil {
		return nil, nil, fmt.Errorf("failed to load snippets: %v", loadError)
	}
	return snippets, verilogFiles, nil
}

func GetRandomSnippet(verbose int) (*Snippet, error) {
	logger.SetVerboseLevel(verbose)
	snippets, _, err := getSnippets()
	if err != nil {
		return nil, fmt.Errorf("failed to get snippets: %v", err)
	}
	if len(snippets) == 0 {
		return nil, errors.New("no snippets available")
	}

	// Use weighted selection based on scores if available
	return getWeightedRandomSnippet(snippets), nil
}

// getWeightedRandomSnippet selects a snippet using weighted probability based on scores
func getWeightedRandomSnippet(snippets []*Snippet) *Snippet {
	// Count snippets with and without scores
	var totalWeight float64
	weightsMap := make(map[int]float64)

	for i, snippet := range snippets {
		weight := 1.0 // default weight for snippets without scores
		if snippet.Score != nil && snippet.Score.Probability > 0 {
			weight = snippet.Score.Probability
		}
		weightsMap[i] = weight
		totalWeight += weight
	}

	if totalWeight <= 0 {
		// Fallback to uniform random selection
		randomIndex := utils.RandomInt(0, len(snippets)-1)
		return snippets[randomIndex]
	}

	// Generate random number between 0 and totalWeight
	target := utils.RandomFloat64() * totalWeight

	// Find the snippet that corresponds to this weight
	cumulative := 0.0
	for i, snippet := range snippets {
		cumulative += weightsMap[i]
		if target <= cumulative {
			return snippet
		}
	}

	// Fallback (should not reach here)
	return snippets[len(snippets)-1]
}

// loadScoreFile reads a .sscr file for a snippet and returns the score
func loadScoreFile(snippetFilePath, moduleName string) (*SnippetScore, error) {
	// Determine score file path: replace .sv with .sscr
	dir := filepath.Dir(snippetFilePath)
	base := strings.TrimSuffix(filepath.Base(snippetFilePath), ".sv")
	scoreFilePath := filepath.Join(dir, base+".sscr")

	content, err := os.ReadFile(scoreFilePath)
	if err != nil {
		return nil, fmt.Errorf("failed to read score file %s: %v", scoreFilePath, err)
	}

	lines := strings.Split(strings.TrimSpace(string(content)), "\n")
	if len(lines) != 6 {
		return nil, fmt.Errorf(
			"score file %s should contain exactly 6 lines, got %d",
			scoreFilePath,
			len(lines),
		)
	}

	// Parse the 6 numbers
	values := make([]int, 6)
	for i, line := range lines {
		val, err := strconv.Atoi(strings.TrimSpace(line))
		if err != nil {
			return nil, fmt.Errorf(
				"failed to parse line %d in score file %s: %v",
				i+1,
				scoreFilePath,
				err,
			)
		}
		values[i] = val
	}

	score := &SnippetScore{
		NumSimulators:    values[0],
		NumSynthesizers:  values[1],
		SimulatorScore:   values[2],
		SynthesizerScore: values[3],
		MaximalScore:     values[4],
		ReachedScore:     values[5],
	}

	// Calculate probability
	if score.MaximalScore > 0 {
		score.Probability = float64(score.ReachedScore) / float64(score.MaximalScore)
	} else {
		score.Probability = 0.0
	}

	return score, nil
}

// WriteScoreFile writes a score to a .sscr file
func WriteScoreFile(snippetFilePath string, score *SnippetScore) error {
	// Determine score file path: replace .sv with .sscr
	dir := filepath.Dir(snippetFilePath)
	base := strings.TrimSuffix(filepath.Base(snippetFilePath), ".sv")
	scoreFilePath := filepath.Join(dir, base+".sscr")

	content := fmt.Sprintf("%d\n%d\n%d\n%d\n%d\n%d\n",
		score.NumSimulators,
		score.NumSynthesizers,
		score.SimulatorScore,
		score.SynthesizerScore,
		score.MaximalScore,
		score.ReachedScore,
	)

	return os.WriteFile(scoreFilePath, []byte(content), 0o644)
}

// dfsDependencies recursively traverses the dependency graph of a Verilog file
// and adds dependencies to the target file's dependency map.
// It ensures that all dependencies are captured, including those from parent files.
// It also copies structs, classes, modules, interfaces, and packages from the parent file to the target file.
func dfsDependencies(
	nodeName string,
	parentVF *verilog.VerilogFile,
	targetFile *verilog.VerilogFile,
) {
	parentNode, ok := parentVF.DependencyMap[nodeName]
	if !ok {
		return
	}

	for _, dep := range parentNode.DependsOn {
		if _, found := targetFile.DependencyMap[dep]; found {
			targetFile.AddDependency(nodeName, dep)
			continue
		}
		targetFile.DependencyMap[dep] = parentVF.DependencyMap[dep]
		if s, found := parentVF.Structs[dep]; found {
			if _, exists := targetFile.Structs[dep]; !exists {
				targetFile.Structs[dep] = s
			}
		}
		if c, found := parentVF.Classes[dep]; found {
			if _, exists := targetFile.Classes[dep]; !exists {
				targetFile.Classes[dep] = c
			}
		}
		if m, found := parentVF.Modules[dep]; found {
			if _, exists := targetFile.Modules[dep]; !exists {
				targetFile.Modules[dep] = m
			}
		}
		if i, found := parentVF.Interfaces[dep]; found {
			if _, exists := targetFile.Interfaces[dep]; !exists {
				targetFile.Interfaces[dep] = i
			}
		}
		if p, found := parentVF.Packages[dep]; found {
			if _, exists := targetFile.Packages[dep]; !exists {
				targetFile.Packages[dep] = p
			}
		}
		dfsDependencies(dep, parentVF, targetFile)
	}
}

func AddDependenciesOfSnippet(targetFile *verilog.VerilogFile, snippet *Snippet) error {
	return GeneralAddDependencies(targetFile, snippet, false)
}

func AddDependencies(targetFile *verilog.VerilogFile, snippet *Snippet) error {
	return GeneralAddDependencies(targetFile, snippet, true)
}

// GeneralAddDependencies adds dependencies of a snippet to the target file.
// If addItself is true, it also adds the snippet's module to the target file
// and updates the dependency map accordingly.
// If addItself is false, it only adds the dependencies without adding the module.
func GeneralAddDependencies(
	targetFile *verilog.VerilogFile,
	snippet *Snippet,
	addItself bool,
) error {
	if snippet.ParentFile == nil {
		return errors.New("snippet parent file is nil")
	}
	if targetFile.DependencyMap == nil {
		targetFile.DependencyMap = make(map[string]*verilog.DependencyNode)
	}
	if _, ok := targetFile.DependencyMap[snippet.Module.Name]; !ok && addItself {
		parentNode := snippet.ParentFile.DependencyMap[snippet.Module.Name]
		targetFile.DependencyMap[snippet.Module.Name] = &verilog.DependencyNode{
			Name:       snippet.Module.Name,
			DependsOn:  append([]string{}, parentNode.DependsOn...),
			DependedBy: append([]string{}, parentNode.DependedBy...),
		}
	}
	if addItself {
		targetFile.Modules[snippet.Module.Name] = snippet.Module
	}

	dfsDependencies(snippet.Name, snippet.ParentFile, targetFile)

	return nil
}
