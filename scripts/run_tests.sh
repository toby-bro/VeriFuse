#!/bin/bash
# filepath: /home/jns/Documents/Berkeley/pfuzz/scripts/run_tests.sh

set -e  # Exit on any error

# Ensure we have the pfuzz binary
if [ ! -f ./pfuzz ]; then
    echo "Building pfuzz..."
    go build -o pfuzz cmd/pfuzz/main.go
fi

# Create test directories if they don't exist
mkdir -p testfiles/sv
mkdir -p tmp_gen

# List of test files to run
# Get list of test files as an array
TEST_FILES=()
while IFS= read -r line; do
    TEST_FILES+=("$line")
done < <(find testfiles/sv/ -name '*.sv' -type f ! -path '*/unsupported/*' ! -path '*/fail/*' ! -path '*/mock/*' -print | sort)

# Test each file individually
PASS_COUNT=0
FAIL_COUNT=0
TOTAL_COUNT=${#TEST_FILES[@]}

echo "===== Running tests on ${TOTAL_COUNT} test files ====="

for test_file in "${TEST_FILES[@]}"; do
    echo -n "Testing ${test_file}... "
    
    # Clean temporary files
    rm -rf tmp_gen/* mismatches/* debug_logs/*
    
    # Run the pfuzz command with limited tests
    if ./pfuzz -n 10 -strategy simple -workers 1 -file "$test_file" &> /tmp/pfuzz_test_output; then
        echo "[PASS]"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo "[FAIL]"
        echo "Error output:"
        cat /tmp/pfuzz_test_output
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
done

# Print summary
echo "===== Test results ====="
echo "Passed: ${PASS_COUNT}/${TOTAL_COUNT}"
echo "Failed: ${FAIL_COUNT}/${TOTAL_COUNT}"

# Exit with proper code
if [ $FAIL_COUNT -eq 0 ]; then
    echo "All tests passed!"
    exit 0
else
    echo "Some tests failed."
    exit 1
fi