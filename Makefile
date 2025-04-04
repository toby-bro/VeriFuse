.PHONY: all build run clean purge analyze patterns focused help

# Default target builds and runs basic fuzzer
all: build run

# Build all tools
build: build-fuzzer build-tools

# Build the main fuzzer
build-fuzzer:
	go build -o pfuzz cmd/pfuzz/main.go

# Build additional analysis tools
build-tools: build-analyze build-patterns build-focused

build-analyze:
	go build -o analyze cmd/analyze/main.go

build-patterns:
	go build -o patterns cmd/patterns/main.go

build-focused:
	go build -o focused cmd/focused/main.go

# Run fuzzer with default settings
run: clean
	./pfuzz -n 1 -strategy smart -workers 1 -v -file ibex_branch_predict.sv

# Run analysis tools
analyze-mismatch:
	@if [ -z "$(MISMATCH)" ]; then \
		echo "Usage: make analyze-mismatch MISMATCH=mismatches/mismatch_X"; \
	else \
		./analyze $(MISMATCH); \
	fi

patterns:
	./patterns

focused:
	./focused

# Clean up temporary directories
clean:
	rm -rf tmp_gen mismatches debug_logs *.json

# Completely remove all generated files
purge: clean
	rm -f pfuzz analyze patterns focused mismatch_*.txt

# Help information
help:
	@echo "Available targets:"
	@echo "  make              - Build and run basic fuzzer"
	@echo "  make build        - Build all tools"
	@echo "  make run          - Run fuzzer"
	@echo "  make clean        - Remove temporary files"
	@echo "  make purge        - Remove all generated files and executables"
	@echo "  make analyze-mismatch MISMATCH=mismatches/mismatch_X - Analyze a specific mismatch"
	@echo "  make patterns     - Analyze patterns in mismatches"
	@echo "  make focused      - Run focused test cases"
	@echo ""
	@echo "Example usage:"
	@echo "  make              - Run default fuzzer"
	@echo "  make run OPTS=\"-n 100 -strategy simple -v\" - Run with custom options"
	@echo "  make analyze-mismatch MISMATCH=mismatches/mismatch_0 - Analyze first mismatch"

# Allow passing custom options to the fuzzer
ifneq ($(OPTS),)
run: clean
	./pfuzz $(OPTS)
endif