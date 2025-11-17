# Justfile for pfuzz mismatch analysis commands

# Set shell to zsh
set shell := ["zsh", "-c"]
set working-directory := "mismatches"

# Variables
script_dir := justfile_directory() + "/scripts"
default_file := shell('cd ' + invocation_directory() + ' && if [[ $(pwd | grep -c "worker_") -gt 0 ]]; then cd $(pwd | grep -Po "^.*/worker_[\d_]+") && basename $(find . -maxdepth 1 -name "*.sv" -not -name "*-Yosys.sv" -not -name "*-SV2V.sv" -not -name "testbench.*" | grep -oP "(?<=\\./)[^/]*(?=\\.sv)" | sort | head -1); else basename $(find . -maxdepth 2 -path "./worker_*" -name "*.sv" -not -name "*-Yosys.sv" -not -name "*-SV2V.sv" -not -name "testbench.*" | grep -oP "(?<=\\./).*?(?=\\.sv)" | sort | head -1); fi')

# Default recipe - show available commands
default:
    @just --list

count:
    ls . | wc -l

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

# Find files that reference a given file
find-references file=default_file:
    find . -maxdepth 2 -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' -exec grep -l {{file}} {} \;

# Simulator operations

# Run Verilator simulation
[no-cd]
verilator path="." file=default_file:
    verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert \
        -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH \
        -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED \
        -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER \
        {{path}}/testbench.sv -O3 -I {{path}}/{{file}}.sv && ./obj_dir/Vtestbench

# Run Yosys synthesis and simulation
[no-cd]
yosys path="." file=default_file:
    yosys -q -p "read_verilog -sv {{path}}/{{file}}.sv; prep -top {{file}} ; write_cxxrtl -O3 {{file}}.cc"
    g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench {{path}}/testbench.cpp && ./testbench

# Run yosys slang synthesis and simulation
[no-cd]
yosys-slang path="." file=default_file:
    yosys -m slang -q -p "read_slang {{path}}/{{file}}.sv --top {{file}}; prep -top {{file}} ; write_cxxrtl -O3 {{file}}.cc"
    g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench {{path}}/testbench.cpp && ./testbench

# Run iverilog simulation  
[no-cd]
iverilog path='.' file=default_file:
    iverilog -o module_sim_iv -g2012 -gsupported-assertions {{path}}/testbench.sv {{path}}/{{file}}.sv && ./module_sim_iv

# Reproduce mismatch by running all simulators and comparing outputs
[no-cd]
reproduce *args:
    #!/usr/bin/env zsh
    if [[ -f "testbench.sv" ]]; then
        {{script_dir}}/reproduce.sh {{args}}
    else
        echo "Error: testbench.sv not found in current directory"
        echo "Make sure you're in a worker directory with a testbench.sv file"
        exit 1
    fi

# Mismatch analysis

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

# Move directories with a specific grep pattern to a target directory
move-mismatch-pattern-matches pattern targetdir:
    #!/usr/bin/env zsh
    echo "Starting to move directories matching pattern '{{pattern}}' to '{{targetdir}}'..."
    if [[ ! -d "{{targetdir}}" ]]; then
        echo "Target directory '{{targetdir}}' does not exist. Creating it..."
        mkdir -p "{{targetdir}}"
    fi
    targetdir=$(realpath "{{targetdir}}") || exit 1
    cd {{justfile_directory()}}/mismatches
    find . -path './worker_*' -name 'mismatch_*_summary.txt' -exec grep -lP "{{pattern}}" {} + | while read -r file; do
        dir=$(dirname "$file")
        if [[ -d "$dir" ]]; then
            echo "Moving $dir to $targetdir/"
            mv "$dir" "$targetdir/"
        fi
    done
    echo "Completed moving directories matching pattern '{{pattern}}' to $targetdir/"

move-svfile-pattern-matches pattern targetdir:
    #!/usr/bin/env zsh
    echo "Starting to move directories with .sv files matching pattern '{{pattern}}' to '{{targetdir}}'..."
    if [[ ! -d "{{targetdir}}" ]]; then
        echo "Target directory '{{targetdir}}' does not exist. Creating it..."
        mkdir -p "{{targetdir}}"
    fi
    targetdir=$(realpath "{{targetdir}}") || exit 1
    cd {{justfile_directory()}}/mismatches
    find . -path './worker_*' -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' -exec grep -lP "{{pattern}}" {} + | while read -r file; do
        dir=$(dirname "$file")
        if [[ -d "$dir" ]]; then
            echo "Moving $dir to $targetdir/"
            mv "$dir" "$targetdir/"
        fi
    done
    echo "Completed moving directories with .sv files matching pattern '{{pattern}}' to $targetdir/"

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

# Generate a testbench for the file (use the args -d /foo/bar to specify output directory, if none will print to stdout)
[no-cd]
generate-testbench file *args:
    {{justfile_directory()}}/testbench {{file}} {{args}}

# Convert testbench to hardcoded values (no file I/O)
[no-cd]
hardcode file="testbench.sv" *args:
    {{script_dir}}/hardcode.sh {{args}} {{file}}

# Hardcode and replace the testbench file
[no-cd]
hardcode-inplace file="testbench.sv" *args:
    {{script_dir}}/hardcode.sh {{args}} {{file}} {{file}}
