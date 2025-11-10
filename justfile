# Justfile for pfuzz mismatch analysis commands

# Set shell to zsh
set shell := ["zsh", "-c"]
set working-directory := "mismatches"

# Variables
script_dir := justfile_directory() + "/scripts"
default_file := shell('cd ' + invocation_directory() + ' && if [[ $(basename $(pwd) | grep -c "worker_") -gt 0 ]]; then basename $(find . -maxdepth 1 -name "*.sv" -not -name "*-Yosys.sv" -not -name "*-SV2V.sv" -not -name "testbench.*" | grep -oP "(?<=\\./)[^/]*(?=\\.sv)" | sort | head -1); else basename $(find . -maxdepth 2 -path "./worker_*" -name "*.sv" -not -name "*-Yosys.sv" -not -name "*-SV2V.sv" -not -name "testbench.*" | grep -oP "(?<=\\./).*?(?=\\.sv)" | sort | head -1); fi')

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
[no-cd]
count-lines file=default_file:
    #!/usr/bin/env zsh
    cd {{justfile_directory()}}/mismatches
    find . -maxdepth 2 -name "{{file}}.sv" -exec wc -l {} + | sort -n

# Move file directories to a target directory (creates target if it doesn't exist)
[no-cd]
move-to-fixed targetdir file=default_file:
    #!/usr/bin/env zsh
    # Check if target directory exists, if not create it
    echo "Starting to move directories containing {{file}}.sv to '{{targetdir}}'..."
    # get absolute path of targetdir
    if [[ ! -d "{{targetdir}}" ]]; then
        echo "Target directory '{{targetdir}}' does not exist. Creating it..."
        mkdir -p "{{targetdir}}"
    fi
    targetdir=$(realpath "{{targetdir}}") || exit 1
    # Find and move the directories one by one
    cd {{justfile_directory()}}/mismatches
    find . -maxdepth 2 -name "{{file}}.sv" -exec dirname {} \; | while read -r dir; do
        if [[ -d "$dir" ]]; then
            echo "Moving $dir to $targetdir/"
            mv "$dir" "$targetdir/"
        fi
    done
    echo "Completed moving directories containing {{file}}.sv to $targetdir/"

# Find files that reference a given file
[no-cd]
find-references file=default_file:
    cd {{justfile_directory()}}/mismatches
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

# Reproduce mismatch by running all simulators and comparing outputs
[no-cd]
reproduce:
    #!/usr/bin/env zsh
    if [[ -f "testbench.sv" ]]; then
        {{script_dir}}/reproduce.sh
    else
        echo "Error: testbench.sv not found in current directory"
        echo "Make sure you're in a worker directory with a testbench.sv file"
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
[no-cd]
show-current-file:
    @echo "Current default file: $(just find-file)"

# List all .sv files in worker directories (excluding generated ones)
list-sv-files:
    find . -maxdepth 2 -path './worker_*' -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | sort

