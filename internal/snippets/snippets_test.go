package snippets

import "testing"

func TestGetSnippets(t *testing.T) {
	snippets, _, err := getSnippets()
	if err != nil {
		t.Fatalf("getSnippets failed: %v", err)
	}
	if len(snippets) == 0 {
		t.Fatalf("getSnippets returned no snippets")
	}
}
