package utils

import "log"

type DebugLogger struct {
	verbose int
}

// verbose level 0: only errors
// verbose level 1: errors and warnings
// verbose level 2: errors, warnings and log messages
// verbose level 3: errors, warnings, log messages and debug messages
// verbose level 4: errors, warnings, log messages, debug messages and all messages

func NewDebugLogger(verbose int) *DebugLogger {
	return &DebugLogger{verbose: verbose}
}

func (d *DebugLogger) Debug(format string, v ...interface{}) {
	if d.verbose > 3 {
		log.Printf("DEBUG: "+format, v...)
	}
}

func (d *DebugLogger) Info(format string, v ...interface{}) {
	if d.verbose > 2 {
		log.Printf("INFO: "+format, v...)
	}
}

func (d *DebugLogger) Warn(format string, v ...interface{}) {
	if d.verbose > 1 {
		log.Printf("WARN: "+format, v...)
	}
}

func (d *DebugLogger) Error(format string, v ...interface{}) {
	if d.verbose > 0 {
		log.Printf("ERROR: "+format, v...)
	}
}

func (d *DebugLogger) Fatal(format string, v ...interface{}) {
	log.Fatalf("FATAL: "+format, v...)
}
