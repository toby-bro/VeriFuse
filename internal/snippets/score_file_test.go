package snippets

import (
	"testing"
)

func TestScoreFileReadWrite(t *testing.T) {
	// Test score file writing and reading
	testScore := &SnippetScore{
		NumSimulators:    2,
		NumSynthesizers:  1,
		SimulatorScore:   3,
		SynthesizerScore: 1,
		MaximalScore:     5, // 2*2 + 1 = 5
		ReachedScore:     4, // 3 + 1 = 4
		Probability:      0.8, // 4/5 = 0.8
	}
	
	tempFile := "/tmp/test_snippet.sv"
	
	// Write score file
	err := WriteScoreFile(tempFile, testScore)
	if err != nil {
		t.Fatalf("Failed to write score file: %v", err)
	}
	
	// Read score file back
	loadedScore, err := loadScoreFile(tempFile, "test_module")
	if err != nil {
		t.Fatalf("Failed to read score file: %v", err)
	}
	
	// Verify all fields match
	if loadedScore.NumSimulators != testScore.NumSimulators {
		t.Errorf("NumSimulators mismatch: got %d, want %d", loadedScore.NumSimulators, testScore.NumSimulators)
	}
	if loadedScore.NumSynthesizers != testScore.NumSynthesizers {
		t.Errorf("NumSynthesizers mismatch: got %d, want %d", loadedScore.NumSynthesizers, testScore.NumSynthesizers)
	}
	if loadedScore.SimulatorScore != testScore.SimulatorScore {
		t.Errorf("SimulatorScore mismatch: got %d, want %d", loadedScore.SimulatorScore, testScore.SimulatorScore)
	}
	if loadedScore.SynthesizerScore != testScore.SynthesizerScore {
		t.Errorf("SynthesizerScore mismatch: got %d, want %d", loadedScore.SynthesizerScore, testScore.SynthesizerScore)
	}
	if loadedScore.MaximalScore != testScore.MaximalScore {
		t.Errorf("MaximalScore mismatch: got %d, want %d", loadedScore.MaximalScore, testScore.MaximalScore)
	}
	if loadedScore.ReachedScore != testScore.ReachedScore {
		t.Errorf("ReachedScore mismatch: got %d, want %d", loadedScore.ReachedScore, testScore.ReachedScore)
	}
	
	// Check probability calculation
	expectedProbability := float64(testScore.ReachedScore) / float64(testScore.MaximalScore)
	if loadedScore.Probability != expectedProbability {
		t.Errorf("Probability mismatch: got %f, want %f", loadedScore.Probability, expectedProbability)
	}
}