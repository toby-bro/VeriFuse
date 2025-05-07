.PHONY: all
all: build run

.PHONY: build
build: build-fuzzer build-tools

.PHONY: build-fuzzer
build-fuzzer:
	go build -o pfuzz cmd/pfuzz/main.go

.PHONY: build-tools
build-tools: build-analyze build-patterns build-focused

.PHONY: build-analyze
build-analyze:
	go build -o analyze cmd/analyze/main.go

.PHONY: build-patterns
build-patterns:
	go build -o patterns cmd/patterns/main.go

.PHONY: build-focused
build-focused:
	go build -o focused cmd/focused/main.go

.PHONY: run
run: test-module

.PHONY: analyze-mismatch
analyze-mismatch:
	@if [ -z "$(MISMATCH)" ]; then \
		echo "Usage: make analyze-mismatch MISMATCH=mismatches/mismatch_X"; \
	else \
		./analyze $(MISMATCH); \
	fi

.PHONY: patterns
patterns:
	./patterns

.PHONY: focused
focused:
	./focused

.PHONY: test-go
test-go: build-fuzzer
	@echo "Running Go tests..."
	@go test -v -parallel 1 -timeout 10s ./...

.PHONY: tests
tests: test-go

.PHONY: lint
lint:
	@echo "Running linters..."
	@golangci-lint run ./... --timeout 10m --color=always --fix

.PHONY: bash-tests
bash-tests: build-fuzzer clean test-go
	@echo "Running tests on SystemVerilog modules..."
	@bash scripts/run_tests.sh

.PHONY: test-fails
test-fails: build-fuzzer clean
	@echo "Running tests on SystemVerilog modules..."
	@bash scripts/run_tests.sh | grep FAIL

.PHONY: test-module
test-module: clean
	@if [ -z "$(FILE)" ]; then \
		echo "Usage: make test-module FILE=path/to/module.sv"; \
	else \
		./pfuzz -n 100 -strategy smart -workers 10 -v -file $(FILE); \
	fi

.PHONY: clean
clean:
	rm -rf tmp_gen mismatches debug_logs *.json

.PHONY: purge
purge: clean
	rm -f pfuzz analyze patterns focused mismatch_*.txt

.PHONY: help
help:
	@echo "Available targets:"
	@echo "  make              - Build and run basic fuzzer"
	@echo "  make build        - Build all tools"
	@echo "  make run          - Run fuzzer"
	@echo "  make tests        - Run all tests"
	@echo "  make clean        - Remove temporary files"
	@echo "  make purge        - Remove all generated files and executables"
	@echo "  make analyze-mismatch MISMATCH=mismatches/mismatch_X - Analyze a specific mismatch"
	@echo "  make patterns     - Analyze patterns in mismatches"
	@echo "  make focused      - Run focused test cases"
	@echo "  make test-module FILE=path/to/module.sv - Test a specific module"
	@echo ""
	@echo "Example usage:"
	@echo "  make              - Run default fuzzer"
	@echo "  make run OPTS=\"-n 100 -strategy simple -v\" - Run with custom options"
	@echo "  make tests        - Run all test cases"
	@echo "  make analyze-mismatch MISMATCH=mismatches/mismatch_0 - Analyze first mismatch"
	@echo "  make test-module FILE=testfiles/sv/simple_adder.sv - Test a specific module"

# Allow passing custom options to the fuzzer
ifneq ($(OPTS),)
run: clean
	./pfuzz $(OPTS)
endif
