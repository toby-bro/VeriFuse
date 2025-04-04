package utils

import (
	"fmt"
	"math/rand"
	"regexp"
	"strconv"
	"strings"
)

// GenerateRandomBitString generates a Verilog-style random bit string
func GenerateRandomBitString(width int) string {
	val := rand.Uint64() & ((1 << width) - 1)
	return fmt.Sprintf("%d'b%b", width, val)
}

// GenerateRandomHexString generates a Verilog-style random hex string
func GenerateRandomHexString(width int) string {
	bytes := (width + 3) / 4
	val := rand.Uint64() & ((1 << (bytes * 4)) - 1)
	return fmt.Sprintf("%d'h%x", width, val)
}

// InferBitWidth tries to determine bit width from context
func InferBitWidth(context string) int {
	if match := regexp.MustCompile(`\[(\d+):0\]`).FindStringSubmatch(context); match != nil {
		if width, err := strconv.Atoi(match[1]); err == nil {
			return width + 1
		}
	}

	switch {
	case strings.Contains(context, "opcode"):
		return 7
	case strings.Contains(context, "branch"):
		return 3
	default:
		return rand.Intn(32) + 1
	}
}

// RemoveComments removes all comments from SystemVerilog code
func RemoveComments(content string) string {
	// First, remove single-line comments
	singleLineCommentRegex := regexp.MustCompile(`//.*$`)
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		lines[i] = singleLineCommentRegex.ReplaceAllString(line, "")
	}
	content = strings.Join(lines, "\n")

	// Then, remove multi-line comments
	multiLineCommentRegex := regexp.MustCompile(`/\*[\s\S]*?\*/`)
	content = multiLineCommentRegex.ReplaceAllString(content, "")

	// Clean up any empty lines
	emptyLineRegex := regexp.MustCompile(`\n\s*\n`)
	for emptyLineRegex.MatchString(content) {
		content = emptyLineRegex.ReplaceAllString(content, "\n")
	}

	return content
}

// RemoveUniqueCases replaces "unique case" with "case"
func RemoveUniqueCases(content string) string {
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		if strings.Contains(line, "unique case") {
			lines[i] = strings.Replace(line, "unique case", "case", 1)
		}
	}
	return strings.Join(lines, "\n")
}
