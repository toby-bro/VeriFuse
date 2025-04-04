package utils

import "log"

// DebugLogger handles conditional DEBUG logging
type DebugLogger struct {
	verbose bool
}

// NewDebugLogger creates a new debug logger
func NewDebugLogger(verbose bool) *DebugLogger {
	return &DebugLogger{verbose: verbose}
}

// Printf prints debug messages if verbose mode is enabled
func (d *DebugLogger) Printf(format string, v ...interface{}) {
	if d.verbose {
		log.Printf("DEBUG: "+format, v...)
	}
}

// Log prints normal (non-debug) messages
func (d *DebugLogger) Log(format string, v ...interface{}) {
	log.Printf(format, v...)
}
