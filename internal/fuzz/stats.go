package fuzz

import (
	"fmt"
	"log"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// Stats tracks statistics about the fuzzing run
type Stats struct {
	TotalTests     int
	Mismatches     int
	SimErrors      int
	mutex          sync.Mutex
	FoundMutants   map[string]bool            // Track unique mismatches
	LastMismatches []map[*verilog.Port]string // Store recent mismatches
}

// NewStats creates a new Stats instance
func NewStats() *Stats {
	return &Stats{
		FoundMutants:   make(map[string]bool),
		LastMismatches: make([]map[*verilog.Port]string, 0),
	}
}

// AddMismatch records a mismatch
func (fs *Stats) AddMismatch(tc map[*verilog.Port]string) {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.Mismatches++

	// Create a unique key for this mismatch by combining input values
	var key string
	for k, v := range tc {
		key += fmt.Sprintf("%s=%s_", k, v)
	}

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

func (fs *Stats) AddCompilationMismatch() {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.Mismatches++
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
	fmt.Printf("Mismatches found: %d\n", fs.Mismatches)
	fmt.Printf("Unique mismatch types: %d\n", len(fs.FoundMutants))

	if len(fs.LastMismatches) > 0 {
		fmt.Printf("\nLast %d unique mismatches:\n", len(fs.LastMismatches))
		for i, tc := range fs.LastMismatches {
			fmt.Printf("%d: ", i+1)
			for k, v := range tc {
				fmt.Printf("%s=%s ", k, v)
			}
			fmt.Println()
		}
	}
}

// ProgressTracker tracks and reports fuzzing progress
type ProgressTracker struct {
	numTests     int
	stats        *Stats
	done         chan struct{}
	ticker       *time.Ticker
	wg           *sync.WaitGroup // Add WaitGroup to monitor worker completion
	timeout      time.Duration   // Maximum time to wait for workers
	lastProgress int             // Track last known progress to detect hangs
	hangDetector *time.Ticker    // Ticker to detect if progress has stalled
}

// NewProgressTracker creates a new progress tracker
func NewProgressTracker(numTests int, stats *Stats, wg *sync.WaitGroup) *ProgressTracker {
	return &ProgressTracker{
		numTests:     numTests,
		stats:        stats,
		done:         make(chan struct{}),
		ticker:       time.NewTicker(5 * time.Second),
		wg:           wg,               // Store wg
		timeout:      10 * time.Minute, // 10 minute overall timeout
		lastProgress: 0,
		hangDetector: time.NewTicker(30 * time.Second), // Check for hangs every 30 seconds
	}
}

// Start begins tracking progress
func (pt *ProgressTracker) Start() {
	allWorkersDone := make(chan struct{})
	overallTimeout := time.After(pt.timeout)

	// Goroutine to wait for all workers to finish and then signal
	if pt.wg != nil {
		go func() {
			pt.wg.Wait()
			close(allWorkersDone)
		}()
	}

	go func() {
		defer pt.ticker.Stop()       // Ensure ticker is stopped when this goroutine exits
		defer pt.hangDetector.Stop() // Stop hang detector

		for {
			select {
			case <-pt.ticker.C:
				// Progress message updated to not include SimErrors
				log.Printf("Progress: %d/%d tests run, %d mismatches found\n",
					pt.stats.TotalTests, pt.numTests, pt.stats.Mismatches)

			case <-pt.hangDetector.C:
				// Check if progress has stalled
				currentProgress := pt.stats.TotalTests
				if currentProgress == pt.lastProgress && currentProgress < pt.numTests {
					log.Printf(
						"Warning: No progress detected for 30 seconds. Current: %d/%d tests, last: %d",
						currentProgress,
						pt.numTests,
						pt.lastProgress,
					)
				}
				pt.lastProgress = currentProgress

			case <-overallTimeout:
				log.Printf(
					"Error: Overall timeout (%v) reached. Forcing termination. Progress: %d/%d tests run, %d mismatches found",
					pt.timeout,
					pt.stats.TotalTests,
					pt.numTests,
					pt.stats.Mismatches,
				)
				log.Printf(
					"This indicates workers are hanging or taking too long. Consider investigating worker logs.",
				)
				return // Force exit on timeout

			case <-allWorkersDone:
				// All workers have completed. Print a final status from the tracker's perspective.
				log.Printf(
					"All workers have completed. Final progress update from tracker: %d/%d tests run, %d mismatches found\n",
					pt.stats.TotalTests,
					pt.numTests,
					pt.stats.Mismatches,
				)
				return // Exit this goroutine; Fuzzer.Run will handle full Stop() via defer.

			case <-pt.done: // Closed by pt.Stop() from Fuzzer.Run's defer
				return // Exit this goroutine
			}
		}
	}()
}

// Stop ends progress tracking
func (pt *ProgressTracker) Stop() {
	// Prevent double closing pt.done
	select {
	case <-pt.done:
		// Already closed or being closed
	default:
		close(pt.done)
	}
}
