package utils

import (
	"fmt"
	"log"
	"os"
)

// ANSI color codes
const (
	ColorReset  = "\033[0m"
	ColorRed    = "\033[31m"
	ColorGreen  = "\033[32m"
	ColorYellow = "\033[33m"
	ColorBlue   = "\033[34m"
	ColorWhite  = "\033[37m"
	ColorGrey   = "\033[90m"
	BoldStart   = "\033[1m"
	BoldEnd     = "\033[22m"
)

const (
	VerbositySilent  = iota // 0: Only Fatal messages are logged.
	VerbosityError          // 1: Error and Fatal messages are logged.
	VerbosityWarning        // 2: Warning, Error, and Fatal messages are logged.
	VerbosityInfo           // 3: Info, Warning, Error, and Fatal messages are logged.
	VerbosityDebug          // 4: Debug, Info, Warning, Error, and Fatal messages are logged.
)

type DebugLogger struct {
	verbose int
	logger  *log.Logger
}

func NewDebugLogger(verbose int) *DebugLogger {
	customLogger := log.New(os.Stdout, "", 0)
	return &DebugLogger{
		verbose: verbose,
		logger:  customLogger,
	}
}

func (d *DebugLogger) Debug(format string, v ...interface{}) {
	if d.verbose >= VerbosityDebug {
		msg := fmt.Sprintf("%s[+] DEBUG:%s", BoldStart, BoldEnd)
		msg += fmt.Sprintf(" "+format, v...)
		d.logger.Print(ColorGrey + msg + ColorReset)
	}
}

func (d *DebugLogger) Info(format string, v ...interface{}) {
	if d.verbose >= VerbosityInfo {
		msg := fmt.Sprintf("%s[+] INFO :%s", BoldStart, BoldEnd)
		msg += fmt.Sprintf(" "+format, v...)
		d.logger.Print(ColorGreen + msg + ColorReset)
	}
}

func (d *DebugLogger) Warn(format string, v ...interface{}) {
	if d.verbose >= VerbosityWarning {
		msg := fmt.Sprintf("%s[+] WARN :%s", BoldStart, BoldEnd)
		msg += fmt.Sprintf(" "+format, v...)
		d.logger.Print(ColorYellow + msg + ColorReset)
	}
}

func (d *DebugLogger) Error(format string, v ...interface{}) {
	if d.verbose >= VerbosityError {
		msg := fmt.Sprintf("%s[+] ERROR:%s", BoldStart, BoldEnd)
		msg += fmt.Sprintf(" "+format, v...)
		d.logger.Print(ColorRed + msg + ColorReset)
	}
}

func (d *DebugLogger) Fatal(format string, v ...interface{}) {
	msg := fmt.Sprintf("%s[+] FATAL:%s", BoldStart, BoldEnd)
	msg += fmt.Sprintf(" "+format, v...)
	d.logger.Print(ColorRed + msg + ColorReset)
	os.Exit(1)
}
