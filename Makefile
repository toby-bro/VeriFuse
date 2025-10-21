.PHONY: all
all: build run

.PHONY: build
build: build-fuzzer build-testbench pre-commit-hook build-generate

GOBUILDFILES=$(shell find . -name '*.go' -not -path './cmd/*' -not -name '*_test.go')
GOTESTFILES=$(shell find . -name '*_test.go')
ALLGOFILES=$(shell find . -name '*.go')
SVFILES=$(shell find snippets -name '*.sv')

.PHONY: pre-commit-hook
pre-commit-hook: .pre-commit
	@chmod +x .pre-commit
	@ln -sf ../../.pre-commit .git/hooks/pre-commit
	@echo "Pre-commit hook installed"

.PHONY: build-fuzzer
build-fuzzer: pfuzz

pfuzz: cmd/pfuzz/main.go $(GOBUILDFILES)
	go build -o pfuzz cmd/pfuzz/main.go

.PHONY: build-testbench
build-testbench: testbench

testbench: cmd/testbench/main.go $(GOBUILDFILES)
	go build -o testbench cmd/testbench/main.go

.PHONY: build-generate
build-generate: generate

generate: cmd/generate/main.go $(GOBUILDFILES)
	go build -o generate cmd/generate/main.go

.test-go.log: pfuzz $(GOTESTFILES)
	@echo "Running Go tests..."
	@go test -parallel 1 -timeout 120s ./...
	@touch .test-go.log

.PHONY: tests
tests: .test-go.log

.PHONY: lint
lint: .lint.log

.lint.log: $(ALLGOFILES) $(SVFILES)
	@echo "Running linters..."
	@golangci-lint run ./... --timeout 20s --color=always --fix
	@find snippets -name '*.sv' -exec ./scripts/fix-indent.sh {} \;
	@touch .lint.log

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

.PHONY: removeKnown
removeKnown:
	rm -r `find mismatches -name '*_inj_o_done*' -exec dirname {} \;`
	rm -r `find mismatches -name '*_inj_data_reg*' -exec dirname {} \;`
	rm -r `find mismatches -name '*_inj_count_out_*.hex' -exec dirname {} \;`
