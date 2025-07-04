.PHONY: all
all: build run

.PHONY: build
build: build-fuzzer build-testbench

.PHONY: build-fuzzer
build-fuzzer: pfuzz

pfuzz: cmd/pfuzz/main.go
	go build -o pfuzz cmd/pfuzz/main.go

.PHONY: build-testbench
build-testbench: testbench

testbench: cmd/testbench/main.go
	go build -o testbench cmd/testbench/main.go

.PHONY: test-go
test-go: build-fuzzer
	@echo "Running Go tests..."
	@go test -parallel 1 -timeout 120s ./...

.PHONY: tests
tests: test-go

.PHONY: lint
lint:
	@echo "Running linters..."
	@golangci-lint run ./... --timeout 10s --color=always --fix
	@find snippets -name '*.sv' -exec ./scripts/fix-indent.sh {} \;

.PHONY: clean
clean:
	rm -rf dist mismatches debug_logs *.json

.PHONY: purge
purge: clean
	rm -f pfuzz patterns mismatch_*.txt

.PHONY: help
help:
	@echo "Available targets:"
	@echo "  make              - Build and run basic fuzzer"
	@echo "  make build        - Build all tools"
	@echo "  make run          - Run fuzzer"
	@echo "  make tests        - Run all tests"
	@echo "  make clean        - Remove temporary files"
	@echo "  make purge        - Remove all generated files and executables"
	@echo "  make patterns     - Analyze patterns in mismatches"
	@echo "  make test-module FILE=path/to/module.sv - Test a specific module"
	@echo ""
	@echo "Example usage:"
	@echo "  make              - Run default fuzzer"
	@echo "  make run OPTS=\"-n 100 -strategy simple -vvv\" - Run with custom options"
	@echo "  make tests        - Run all test cases"
	@echo "  make test-module FILE=testfiles/sv/simple_adder.sv - Test a specific module"

# Allow passing custom options to the fuzzer
ifneq ($(OPTS),)
run: clean
	./pfuzz $(OPTS)
endif

.PHONY: checkSnippets
checkSnippets:
	for i in snippets/*.sv ; do ss=$$(pfuzz -strategy smart -check-file -vv -file $$i 2>/dev/null) ; if [ $$? -eq 0 ]; then echo "[+] success" $$i ; else echo "[-] failure" $$i; fi ; done

.PHONY: addValidSnippets
addValidSnippets:
	for i in $$(git status -s | grep -Eo 'snippets/V3\w+\.sv'); do ss=$$(pfuzz -strategy smart -check-file -vv -file $$i 2>/dev/null) ; if [ $$? -eq 0 ]; then echo "[+] success" $$i && git add $$i ; else echo "[-] failure" $$i; fi ; done

.PHONY: isolated
isolated:
	for i in snippets/*.sv ; do ss=$(pfuzz rewrite-as-snippets -strategy smart -vv -file $i) ;if [ $? -eq 0 ]; then echo "[+] success" $i ; else echo "[-] failure" $i; fi ; done
