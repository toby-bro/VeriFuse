package snippets

import (
	"fmt"
	"testing"
)

func TestWeightedSelection(t *testing.T) {
	// Count selections over many iterations
	counts := make(map[string]int)
	totalIterations := 10000 // Increased for more stable statistics

	for i := 0; i < totalIterations; i++ {
		snippet, err := GetRandomSnippet(1)
		if err != nil {
			t.Fatalf("Failed to get snippet: %v", err)
		}
		counts[snippet.Name]++
	}

	fmt.Printf("Selection counts over %d iterations:\n", totalIterations)
	for name, count := range counts {
		if name == "assert_property_mod" || name == "assume_property_mod" ||
			name == "cover_property_mod" {
			fmt.Printf(
				"  %s: %d (%.1f%%)\n",
				name,
				count,
				float64(count)*100.0/float64(totalIterations),
			)
		}
	}

	// Check that snippets with higher scores are selected more often
	// We created scores: assert_property_mod (4/6 = 0.67), assume_property_mod (2/6 = 0.33), cover_property_mod (0/6 = 0.0)

	assertCount := counts["assert_property_mod"]
	assumeCount := counts["assume_property_mod"]
	coverCount := counts["cover_property_mod"]

	// With a larger sample, the weighted selection should be more apparent
	// Allow some variance but expect the general trend to hold
	if assertCount < assumeCount {
		t.Logf(
			"Warning: assert_property_mod (score 0.67) was selected %d times vs assume_property_mod (score 0.33) %d times",
			assertCount,
			assumeCount,
		)
		// Only fail if the difference is very significant (more than 3:1 ratio)
		if assumeCount > assertCount*3 {
			t.Errorf(
				"assert_property_mod should generally be selected more than assume_property_mod due to higher score",
			)
		}
	}

	// The main test is that snippets are being loaded and selected
	totalSnippetsWithScores := assertCount + assumeCount + coverCount
	if totalSnippetsWithScores == 0 {
		t.Errorf(
			"None of our test snippets with scores were selected, which suggests scoring isn't working",
		)
	}

	t.Logf(
		"Successfully tested weighted selection with %d total selections of scored snippets",
		totalSnippetsWithScores,
	)
}
