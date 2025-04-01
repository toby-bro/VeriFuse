package fuzz

import (
	"fmt"
	"log"
	"sync"
	"time"
)

// Stats tracks statistics about the fuzzing run
type Stats struct {
	TotalTests     int
	Mismatches     int
	SimErrors      int
	mutex          sync.Mutex
	FoundMutants   map[string]bool // Track unique mismatches
	LastMismatches []TestCase      // Store recent mismatches
}

// NewStats creates a new Stats instance
func NewStats() *Stats {
	return &Stats{
		FoundMutants:   make(map[string]bool),
		LastMismatches: make([]TestCase, 0),
	}
}

// AddMismatch records a mismatch
func (fs *Stats) AddMismatch(tc TestCase) {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.Mismatches++

	// Create a unique key for this mismatch type
	key := fmt.Sprintf("R%x_P%x_V%d", tc.FetchRdata, tc.FetchPc, tc.FetchValid)

	// Track unique mismatches
	if !fs.FoundMutants[key] {
		fs.FoundMutants[key] = true

		// Keep last N mismatches for reporting
		if len(fs.LastMismatches) >= 5 {
			fs.LastMismatches = fs.LastMismatches[1:]
		}
		fs.LastMismatches = append(fs.LastMismatches, tc)
	}
}

// AddSimError records a simulation error
func (fs *Stats) AddSimError() {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.SimErrors++
}

// AddTest records a test execution
func (fs *Stats) AddTest() {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.TotalTests++
}

// PrintSummary prints a summary of the fuzzing run
func (fs *Stats) PrintSummary() {
	fmt.Printf("\n=== Fuzzing Summary ===\n")
	fmt.Printf("Total test cases: %d\n", fs.TotalTests)
	fmt.Printf("Simulator errors: %d\n", fs.SimErrors)
	fmt.Printf("Mismatches found: %d\n", fs.Mismatches)
	fmt.Printf("Unique mismatch types: %d\n", len(fs.FoundMutants))

	if len(fs.LastMismatches) > 0 {
		fmt.Printf("\nLast %d unique mismatches:\n", len(fs.LastMismatches))
		for i, tc := range fs.LastMismatches {
			fmt.Printf("%d: rdata=0x%08x, pc=0x%08x, valid=%d\n",
				i+1, tc.FetchRdata, tc.FetchPc, tc.FetchValid)
		}
	}
}

// ProgressTracker tracks and reports fuzzing progress
type ProgressTracker struct {
	numTests int
	stats    *Stats
	done     chan struct{}
	ticker   *time.Ticker
}

// NewProgressTracker creates a new progress tracker
func NewProgressTracker(numTests int, stats *Stats) *ProgressTracker {
	return &ProgressTracker{
		numTests: numTests,
		stats:    stats,
		done:     make(chan struct{}),
		ticker:   time.NewTicker(5 * time.Second),
	}
}

// Start begins tracking progress
func (pt *ProgressTracker) Start() {
	go func() {
		for {
			select {
			case <-pt.ticker.C:
				log.Printf("Progress: %d/%d tests run, %d mismatches found\n",
					pt.stats.TotalTests, pt.numTests, pt.stats.Mismatches)
			case <-pt.done:
				pt.ticker.Stop()
				return
			}
		}
	}()
}

// Stop ends progress tracking
func (pt *ProgressTracker) Stop() {
	close(pt.done)
}
