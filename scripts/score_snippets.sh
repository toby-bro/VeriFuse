#!/bin/bash

# Snippet scoring script - alternative to pfuzz score-snippets command
# This script evaluates snippets against available simulators and synthesizers
# and generates .sscr score files

echo "=== Pfuzz Snippet Scoring Script ==="
echo "This script will score all snippets in the isolated/ directory"
echo "against available simulators and synthesizers."
echo ""

# Check if pfuzz binary exists
if [ ! -f "./pfuzz" ]; then
    echo "Error: pfuzz binary not found. Please run 'go build -o pfuzz cmd/pfuzz/main.go' first."
    exit 1
fi

# Check for available tools
echo "Checking available tools..."

# Check simulators
SIMULATORS_AVAILABLE=0
if command -v iverilog >/dev/null 2>&1; then
    echo "  ✓ IVerilog found"
    SIMULATORS_AVAILABLE=$((SIMULATORS_AVAILABLE + 1))
else
    echo "  ✗ IVerilog not found"
fi

if command -v verilator >/dev/null 2>&1; then
    echo "  ✓ Verilator found"
    SIMULATORS_AVAILABLE=$((SIMULATORS_AVAILABLE + 1))
else
    echo "  ✗ Verilator not found"
fi

if command -v yosys >/dev/null 2>&1; then
    echo "  ✓ Yosys found (enables CXXRTL)"
    SIMULATORS_AVAILABLE=$((SIMULATORS_AVAILABLE + 1))
else
    echo "  ✗ Yosys not found (disables CXXRTL)"
fi

# Check synthesizers
SYNTHESIZERS_AVAILABLE=0
if command -v yosys >/dev/null 2>&1; then
    echo "  ✓ Yosys found"
    SYNTHESIZERS_AVAILABLE=$((SYNTHESIZERS_AVAILABLE + 1))
else
    echo "  ✗ Yosys not found"
fi

if command -v sv2v >/dev/null 2>&1; then
    echo "  ✓ SV2V found"
    SYNTHESIZERS_AVAILABLE=$((SYNTHESIZERS_AVAILABLE + 1))
else
    echo "  ✗ SV2V not found"
fi

echo ""
echo "Available tools: $SIMULATORS_AVAILABLE simulators, $SYNTHESIZERS_AVAILABLE synthesizers"

if [ $SIMULATORS_AVAILABLE -eq 0 ] && [ $SYNTHESIZERS_AVAILABLE -eq 0 ]; then
    echo "Warning: No tools available for scoring. Scores will be 0/0."
    echo "To get meaningful scores, install some of the following tools:"
    echo "  - iverilog (for Verilog simulation)"
    echo "  - verilator (for C++ simulation)"
    echo "  - yosys (for synthesis and CXXRTL)"
    echo "  - sv2v (for SystemVerilog to Verilog conversion)"
fi

echo ""
echo "Running snippet scoring..."

# Run the scoring command
./pfuzz score-snippets -v

if [ $? -eq 0 ]; then
    echo ""
    echo "=== Scoring Complete ==="
    echo "Score files (.sscr) have been generated in the isolated/ directory"
    echo "Each .sscr file contains 6 numbers:"
    echo "  1. Number of simulators"
    echo "  2. Number of synthesizers" 
    echo "  3. Simulator score (max 2 per simulator)"
    echo "  4. Synthesizer score (max 1 per synthesizer)"
    echo "  5. Maximum possible score"
    echo "  6. Reached score"
    echo ""
    echo "The probability for snippet injection is: reached_score / max_score"
    echo ""
    
    # Show some example score files if they exist
    echo "Example score files:"
    for sscr_file in isolated/*/*.sscr; do
        if [ -f "$sscr_file" ]; then
            echo "  $sscr_file:"
            cat "$sscr_file" | tr '\n' ' '
            echo ""
            break
        fi
    done
    
    # Count total score files
    SCORE_FILES=$(find isolated/ -name "*.sscr" | wc -l)
    echo "Generated $SCORE_FILES score files total."
    
else
    echo "Error: Scoring failed. Check the output above for details."
    exit 1
fi