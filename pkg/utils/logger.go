package utils

import (
	"fmt"
	"log"
	"os"

	"golang.org/x/term"
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
	verbose   int
	logger    *log.Logger
	errLogger *log.Logger
	isTTY     bool
}

func NewDebugLogger(verbose int) *DebugLogger {
	customLogger := log.New(os.Stdout, "", 0)
	errorLogger := log.New(os.Stderr, "", 0)
	return &DebugLogger{
		verbose:   verbose,
		logger:    customLogger,
		errLogger: errorLogger,
		isTTY:     isTTY(),
	}
}

func (d *DebugLogger) SetVerboseLevel(level int) {
	if level < VerbositySilent || level > VerbosityDebug {
		d.verbose = VerbositySilent
	} else {
		d.verbose = level
	}
}

func (d *DebugLogger) GetVerboseLevel() int {
	return d.verbose
}

func isTTY() bool {
	return term.IsTerminal(int(os.Stdout.Fd())) || term.IsTerminal(int(os.Stderr.Fd()))
}

func bold(s string) string {
	if !isTTY() {
		return s
	}
	return BoldStart + s + BoldEnd
}

func (d *DebugLogger) genPrint(stderr bool, color string, format string, v ...interface{}) {
	msg := fmt.Sprintf(" "+format, v...)
	if d.isTTY {
		msg = color + msg + ColorReset
	}
	if stderr {
		d.errLogger.Print(msg)
	} else {
		d.logger.Print(msg)
	}
}

func (d *DebugLogger) printStdOut(color string, format string, v ...interface{}) {
	d.genPrint(false, color, format, v...)
}

func (d *DebugLogger) printStdErr(color string, format string, v ...interface{}) {
	d.genPrint(true, color, format, v...)
}

func (d *DebugLogger) Debug(format string, v ...interface{}) {
	if d.verbose >= VerbosityDebug {
		msg := bold("[+] DEBUG:")
		msg += fmt.Sprintf(" "+format, v...)
		d.printStdOut(ColorGrey, msg)
	}
}

func (d *DebugLogger) Info(format string, v ...interface{}) {
	if d.verbose >= VerbosityInfo {
		msg := bold("[+] INFO :")
		msg += fmt.Sprintf(" "+format, v...)
		d.printStdOut(ColorGreen, msg)
	}
}

func (d *DebugLogger) Warn(format string, v ...interface{}) {
	if d.verbose >= VerbosityWarning {
		msg := bold("[+] WARN :")
		msg += fmt.Sprintf(" "+format, v...)
		d.printStdOut(ColorYellow, msg)
	}
}

func (d *DebugLogger) Error(format string, v ...interface{}) {
	if d.verbose >= VerbosityError {
		msg := bold("[+] ERROR:")
		msg += fmt.Sprintf(" "+format, v...)
		d.printStdErr(ColorRed, msg)
	}
}

func (d *DebugLogger) Fatal(format string, v ...interface{}) {
	msg := bold("[+] FATAL:")
	msg += fmt.Sprintf(" "+format, v...)
	d.printStdErr(ColorRed, msg)
	os.Exit(1)
}
