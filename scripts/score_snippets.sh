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

if command -v yosys -m slang >/dev/null 2>&1; then
    echo "  ✓ Yosys slang found"
    SIMULATORS_AVAILABLE=$((SIMULATORS_AVAILABLE + 1))
else
    echo "  ✗ Yosys slang not found"
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


for snippet in $(pwd)/isolated/*/*.sv ; do
    if [ -f ${snippet}.sscr ]; then
        # already scored, we skip to the next
        continue
    fi
    sim_score=0
    synth_score=0
    tmp=$(mktemp -d)

    echo ""
    echo "=== Scoring snippet: $snippet ==="
    echo "Processing snippet: $snippet in temporary directory: $tmp"
    snippet_file_base=$(basename "$snippet")
    cp "$snippet" "$tmp/$snippet_file_base"
    ./testbench -d "$tmp" "$snippet"
    (cd $tmp && mkdir iverilog verilator yosys cxxrtl sv2v cxxslg)
    if [ $SIMULATORS_AVAILABLE -gt 0 ]; then
        if command -v iverilog >/dev/null 2>&1; then
            (cd $tmp && iverilog -g2012 -gsupported-assertions -o iverilog/$snippet_file_base.vvp "$snippet_file_base" testbench.sv &>/dev/null)
            if [ $? -eq 0 ]; then
                (cd ${tmp}&& ./iverilog/${snippet_file_base}.vvp &>/dev/null) && echo "IVerilog simulation succeeded for $snippet_file_base"
                sim_score=$((sim_score + 2))
            else
                echo "IVerilog simulation failed for $snippet_file_base"
                sim_score=$((sim_score + 1))
            fi
        fi
        if command -v verilator >/dev/null 2>&1; then
            (cd $tmp/verilator && verilator \
                --binary \
                --exe \
                --build \
                -Mdir obj_dir \
                -sv \
                --timing \
                --assert \
                -Wno-CMPCONST \
                -Wno-DECLFILENAME \
                -Wno-MULTIDRIVEN \
                -Wno-NOLATCH \
                -Wno-LATCH \
                -Wno-UNDRIVEN \
                -Wno-UNOPTFLAT \
                -Wno-UNUSED \
                -Wno-UNSIGNED \
                -Wno-WIDTHEXPAND \
                -Wno-WIDTHTRUNC \
                -Wno-MULTITOP \
                -Wno-CASEINCOMPLETE \
                -Wno-CASEOVERLAP \
                -Wno-ASCRANGE \
                -Wno-CASEX \
                ../testbench.sv \
                ../"$snippet_file_base" \
                &>/dev/null)
            if [ $? -eq 0 ]; then
                (cd ${tmp}/verilator && ./obj_dir/Vtestbench &>/dev/null) && echo "Verilator simulation succeeded for $snippet_file_base"
                sim_score=$((sim_score + 2))
            else
                echo "Verilator simulation failed for $snippet_file_base"
                sim_score=$((sim_score + 1))
            fi
        fi

        # --- CXXRTL simulation (plain) ---
        if command -v yosys &>/dev/null && command -v g++ >/dev/null 2>&1; then
            (cd "$tmp" && yosys -q -p "read_verilog -sv $snippet_file_base; check -assert ; prep -top ${snippet_file_base%.*}; write_cxxrtl cxxrtl/${snippet_file_base%.*}.cc" &>/dev/null)
            if [ $? -ne 0 ]; then
                echo "Yosys CXXRTL generation failed for $snippet_file_base"
            else
                (cd "$tmp"/cxxrtl && g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime ../testbench.cpp -I. -o ${snippet_file_base%.*}_cxxsim )
                if [ -f "$tmp/cxxrtl/${snippet_file_base%.*}_cxxsim" ]; then
                    (cd $tmp/cxxrtl && cp ../input* .)
                    (cd "$tmp"/cxxrtl && ./${snippet_file_base%.*}_cxxsim &>/dev/null)
                    if [ $? -eq 0 ]; then
                        echo "CXXRTL simulation succeeded for $snippet_file_base"
                        sim_score=$((sim_score + 2))
                    else
                        echo "CXXRTL simulation failed for $snippet_file_base"
                        sim_score=$((sim_score + 1))
                    fi
                fi
            fi
        fi

        # --- CXXRTL simulation (with slang) ---
        if command -v yosys &>/dev/null && command -v g++ >/dev/null 2>&1 && yosys -m slang -p 'help' &>/dev/null; then
            (cd "$tmp" && yosys -q -m slang -p "read_slang $snippet_file_base --top ${snippet_file_base%.*}; check -assert ; prep -top ${snippet_file_base%.*}; write_cxxrtl cxxslg/${snippet_file_base%.*}.cc" &>/dev/null)
            if [ $? -ne 0 ]; then
                echo "Yosys CXXRTL slang generation failed for $snippet_file_base"
            else
                (cd "$tmp"/cxxslg && g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime ../testbench.cpp -I. -o ${snippet_file_base%.*}_cxxsim )
                if [ -f "$tmp/cxxslg/${snippet_file_base%.*}_cxxsim" ]; then
                    (cd $tmp/cxxslg && cp ../input* .)
                    (cd "$tmp"/cxxslg && ./${snippet_file_base%.*}_cxxsim &>/dev/null)
                    if [ $? -eq 0 ]; then
                        echo "CXXRTL slang simulation succeeded for $snippet_file_base"
                        sim_score=$((sim_score + 2))
                    else
                        echo "CXXRTL slang simulation failed for $snippet_file_base"
                        sim_score=$((sim_score + 1))
                    fi
                fi
            fi
        fi

        if command -v yosys >/dev/null 2>&1; then
            (cd ${tmp}/yosys && yosys -q -p "read_verilog -sv ${snippet}; check -assert ; prep -top ${snippet_file_base%.*}; synth; write_verilog -noattr $snippet_file_base.v" &>/dev/null)
            if [ $? -eq 0 ]; then
                echo "Yosys synthesis succeeded for $snippet_file_base"
                synth_score=$((synth_score + 1))
            else
                (cd ${tmp}/yosys && yosys -q -m slang -p "read_slang ${snippet} --top ${snippet_file_base%.*}; prep -top ${snippet_file_base%.*}; synth; write_verilog -noattr ${snippet_file_base%.*}.v" &>/dev/null)
                if [ $? -eq 0 ]; then
                    echo "Yosys slang synthesis succeeded for $snippet_file_base"
                    synth_score=$((synth_score + 1))
                else
                    echo "Yosys synthesis failed for $snippet_file_base"
                fi
            fi
        fi
        if command -v sv2v >/dev/null 2>&1; then
            (cd $tmp/sv2v && sv2v --top ${snippet_file_base%.*} ../${snippet_file_base} -w $snippet_file_base.v &>/dev/null)
            if [ $? -eq 0 ]; then
                echo "SV2V conversion succeeded for $snippet_file_base"
                synth_score=$((synth_score + 1))
            else
                echo "SV2V conversion failed for $snippet_file_base"
            fi
        fi
    fi
    # Generate score file
    printf "%s\n%s\n%s\n%s\n%s\n%s\n" "$SIMULATORS_AVAILABLE" "$SYNTHESIZERS_AVAILABLE" "$sim_score" "$synth_score" "$((SIMULATORS_AVAILABLE * 2 + SYNTHESIZERS_AVAILABLE))" "$((sim_score + synth_score))" > "$(dirname "$snippet")/$snippet_file_base.sscr"
    rm -rf "$tmp"
done





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
    
    # Count total score files
    SCORE_FILES=$(find isolated/ -name "*.sscr" | wc -l)
    echo "Generated $SCORE_FILES score files total."
    
else
    echo "Error: Scoring failed. Check the output above for details."
    exit 1
fi