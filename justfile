# Justfile for pfuzz mismatch analysis commands

# Set shell to zsh
set shell := ["zsh", "-c"]
set working-directory := "mismatches"

# Variables
default_file := `basename $(find . -maxdepth 2 -path './worker*' -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | grep -oP '(?<=\./).*?(?=\.sv)' | sort | head -1) 2>/dev/null || echo ""`
script_dir := justfile_directory() + "/scripts"

# Default recipe - show available commands
default:
    @just --list

# FILE operations

# Find and set the FILE variable, show the detected file
[no-cd]
find-file:
    #!/usr/bin/env zsh
    # if i am in a dir that starts with "worker", search only within that dir
    if [[ $(basename $(pwd) | grep -c "worker_") -gt 0 ]]; then
        FILE=`basename $(find . -maxdepth 1 -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | grep -oP '(?<=\./).*?(?=\.sv)' | sort | head -1)`
        echo ${FILE}
        return
    fi
    FILE=`basename $(find . -maxdepth 2 -path './worker_*' -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | grep -oP '(?<=\./).*?(?=\.sv)' | sort | head -1)`
    echo ${FILE}

# Count lines in all versions of a file (sorted by line count)
count-lines file=default_file:
    find . -maxdepth 2 -name "{{file}}.sv" -exec wc -l {} + | sort -n

# Move file directories to a target directory (creates target if it doesn't exist)
move-to-fixed targetdir file=default_file:
    #!/usr/bin/env zsh
    # Check if target directory exists, if not create it
    if [[ ! -d "{{targetdir}}" ]]; then
        echo "Target directory '{{targetdir}}' does not exist. Creating it..."
        mkdir -p "{{targetdir}}"
    else
        echo "Target directory '{{targetdir}}' already exists. Proceeding with move..."
    fi
    # Find and move the directories
    source_dirs=$(find . -maxdepth 2 -name "{{file}}.sv" -exec dirname {} \;)
    if [[ -n "$source_dirs" ]]; then
        mv $source_dirs "{{targetdir}}/"
        echo "Moved directories containing {{file}}.sv to {{targetdir}}/"
    else
        echo "No directories found containing {{file}}.sv"
    fi

# Find files that reference a given file
find-references file=default_file:
    find . -maxdepth 2 -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' -exec grep -l {{file}} {} \;

# Simulator operations

# Run Verilator simulation
[no-cd]
verilator file=default_file:
    #!/usr/bin/env zsh
    verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert \
        -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH \
        -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED \
        -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER \
        ../../testbench.sv-O3 -I ../../{{file}}.sv && ./obj_dir/Vtestbench

# Run Yosys synthesis and simulation
[no-cd]
yosys file=default_file:
    #!/usr/bin/env zsh
    yosys -q -p "read_verilog -sv {{file}}.sv; prep -top {{file}} ; write_cxxrtl -O3 {{file}}.cc"
    g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench testbench.cpp && ./testbench

# Run iverilog simulation  
[no-cd]
iverilog file=default_file:
    #!/usr/bin/env zsh
    iverilog -o module_sim_iv -g2012 -gsupported-assertions ../testbench.sv ../{{file}}.sv && ./module_sim_iv

# Convert testbench to hardcoded values (no file I/O)
[no-cd]
hardcode:
    #!/usr/bin/env zsh
    if [[ -f "testbench.sv" ]]; then
        # if script_dir is a symlink, resolve it to the actual path
        {{script_dir}}/hardcode.sh testbench.sv
    else
        echo "Error: testbench.sv not found in current directory"
        exit 1
    fi

# Mismatch analysis

# Move directories with a specific grep pattern to a target directory
move-pattern-matches pattern targetdir:
    mv $(dirname $(find . -path './worker_*' -name 'mismatch_*_summary.txt' -exec grep -lP '{{pattern}}' {} +) | sort -u) {{targetdir}}

# Clean up build artifacts
clean:
    rm -rf obj_dir module_sim_iv testbench *.cc

# Show current file that would be used by default
show-current-file:
    @echo "Current default file: {{default_file}}"

# List all .sv files in worker directories (excluding generated ones)
list-sv-files:
    find . -maxdepth 2 -path './worker_*' -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | sort