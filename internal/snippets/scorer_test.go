package snippets

import (
	"fmt"
	"testing"
)

func TestWeightedSelection(t *testing.T) {
	// Count selections over many iterations
	counts := make(map[string]int)
	
	for i := 0; i < 1000; i++ {
		snippet, err := GetRandomSnippet(1)
		if err != nil {
			t.Fatalf("Failed to get snippet: %v", err)
		}
		counts[snippet.Name]++
	}
	
	fmt.Println("Selection counts over 1000 iterations:")
	for name, count := range counts {
		fmt.Printf("  %s: %d (%.1f%%)\n", name, count, float64(count)/10.0)
	}
	
	// Check that snippets with higher scores are selected more often
	// We created scores: assert_property_mod (4/6 = 0.67), assume_property_mod (2/6 = 0.33), cover_property_mod (0/6 = 0.0)
	
	assertCount := counts["assert_property_mod"]
	assumeCount := counts["assume_property_mod"]
	coverCount := counts["cover_property_mod"]
	
	// assert_property_mod should be selected most often
	if assertCount <= assumeCount {
		t.Errorf("assert_property_mod (score 0.67) should be selected more than assume_property_mod (score 0.33), got %d vs %d", assertCount, assumeCount)
	}
	
	// cover_property_mod should be selected least (but still some due to default weight)
	if coverCount > assertCount {
		t.Errorf("cover_property_mod (score 0.0) should be selected less than assert_property_mod (score 0.67), got %d vs %d", coverCount, assertCount)
	}
}