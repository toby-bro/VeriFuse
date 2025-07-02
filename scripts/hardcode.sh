#!/bin/bash

# hardcode.sh - Convert testbench file I/O to hardcoded values and display outputs
# Usage: ./hardcode.sh <testbench.sv> [input_dir] [output_file]

set -e

# Function to display usage
usage() {
    echo "Usage: $0 [-v] [-c] <testbench.sv|directory> [output_file]"
    echo ""
    echo "Converts a testbench from file I/O to hardcoded inputs and display outputs"
    echo "Automatically finds suitable input files from test directories"
    echo ""
    echo "Options:"
    echo "  -v                    - Verbose mode (show processing details)"
    echo "  -c                    - Copy testbench to clipboard using wl-copy"
    echo ""
    echo "Arguments:"
    echo "  testbench.sv|directory - Path to testbench file OR directory containing testbench.sv"
    echo "  output_file           - Output file name (optional, prints to stdout if not specified)"
    echo ""
    echo "Examples:"
    echo "  $0 testbench.sv                    # Print to stdout"
    echo "  $0 -v testbench.sv                 # Print to stdout with verbose output"
    echo "  $0 -c testbench.sv                 # Copy to clipboard"
    echo "  $0 -c -v testbench.sv              # Copy to clipboard with verbose output"
    echo "  $0 testbench.sv my_hardcoded_tb.sv # Save to file"
    echo "  $0 /path/to/worker_dir             # Directory with testbench.sv, print to stdout"
    echo "  $0 -v /path/to/worker_dir output.sv # Directory with testbench.sv, save to file, verbose"
    exit 1
}

# Check arguments
if [ $# -lt 1 ]; then
    usage
fi

# Parse options
VERBOSE=false
COPY_TO_CLIPBOARD=false
while getopts "vc" opt; do
    case $opt in
        v)
            VERBOSE=true
            ;;
        c)
            COPY_TO_CLIPBOARD=true
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            usage
            ;;
    esac
done
shift $((OPTIND-1))

# Function for verbose logging
log_verbose() {
    if [ "$VERBOSE" = true ]; then
        echo "$@" >&2
    fi
}

TESTBENCH_INPUT="$1"
OUTPUT_FILE="$2"
USE_STDOUT=false

# Determine if we should output to stdout or clipboard (no output file specified)
if [ -z "$OUTPUT_FILE" ]; then
    if [ "$COPY_TO_CLIPBOARD" = true ]; then
        USE_STDOUT=false
        OUTPUT_FILE=$(mktemp)
    else
        USE_STDOUT=true
        OUTPUT_FILE=$(mktemp)
    fi
fi

# Check if input is a directory or file
if [ -d "$TESTBENCH_INPUT" ]; then
    # It's a directory, look for testbench.sv inside
    TESTBENCH_FILE="$TESTBENCH_INPUT/testbench.sv"
    if [ ! -f "$TESTBENCH_FILE" ]; then
        echo "Error: Directory '$TESTBENCH_INPUT' does not contain a testbench.sv file"
        exit 1
    fi
elif [ -f "$TESTBENCH_INPUT" ]; then
    # It's a file, use it directly
    TESTBENCH_FILE="$TESTBENCH_INPUT"
else
    echo "Error: '$TESTBENCH_INPUT' is neither a valid file nor a directory"
    exit 1
fi

# Get the directory containing the testbench file
TESTBENCH_DIR=$(dirname "$TESTBENCH_FILE")

log_verbose "[+] Processing testbench: $TESTBENCH_FILE"
log_verbose "[+] Looking for test directories in: $TESTBENCH_DIR"

# Function to find required input files from testbench
get_required_inputs() {
    grep -o 'input_[^"]*\.hex' "$TESTBENCH_FILE" | sort -u
}

# Function to find a suitable test directory or generate random inputs
find_input_source() {
    local required_inputs=($(get_required_inputs))
    
    if [ ${#required_inputs[@]} -eq 0 ]; then
        log_verbose "No input files found in testbench"
        return 1
    fi
    
    log_verbose "[+] Required input files: ${required_inputs[*]}"
    
    # Look for test_* directories in the same directory as the testbench
    for test_dir in "$TESTBENCH_DIR"/test_*; do
        if [ -d "$test_dir" ]; then
            log_verbose "  [+] Checking directory: $(basename "$test_dir")"
            
            # Check if this directory has all required input files
            local has_all_files=true
            for input_file in "${required_inputs[@]}"; do
                if [ ! -f "$test_dir/$input_file" ]; then
                    log_verbose "    [!] Missing: $input_file"
                    has_all_files=false
                    break
                fi
            done
            
            if $has_all_files; then
                log_verbose "    [+] Found complete set of input files!"
                echo "FOUND:$test_dir"
                return 0
            fi
        fi
    done
    
    log_verbose "[!] No test directory found with all required input files"
    log_verbose "[+] Will generate random input values instead"
    echo "GENERATE"
    return 0
}

# Function to generate random hex value for a signal
generate_random_hex() {
    local signal_name="$1"
    local width=$(get_signal_width "$signal_name")
    
    # Calculate number of hex digits needed
    local hex_digits
    if [ "$width" == "0" ]; then
        hex_digits=1  # Single bit
    else
        # For width N, we need ceil(N/4) hex digits
        hex_digits=$(( (width + 3) / 4 ))
    fi
    
    # Generate random hex string
    local hex_val=""
    for ((i=0; i<hex_digits; i++)); do
        # Generate random hex digit (0-F)
        local rand_digit=$(printf "%x" $((RANDOM % 16)))
        hex_val="${hex_val}${rand_digit}"
    done
    
    # For single bit signals, make sure we only use 0 or 1
    if [ "$width" == "0" ]; then
        hex_val=$(printf "%x" $((RANDOM % 2)))
    fi
    
    echo "$hex_val"
}

# Find the input directory automatically or prepare for random generation
INPUT_SOURCE=$(find_input_source)
if [ $? -ne 0 ]; then
    exit 1
fi

if [[ "$INPUT_SOURCE" == FOUND:* ]]; then
    INPUT_DIR="${INPUT_SOURCE#FOUND:}"
    log_verbose "[+] Using input directory: $INPUT_DIR"
    USE_RANDOM=false
elif [[ "$INPUT_SOURCE" == "GENERATE" ]]; then
    INPUT_DIR=""
    log_verbose "[+] Will generate random input values"
    USE_RANDOM=true
else
    echo "Error: Unexpected input source result"
    exit 1
fi

# Create a temporary working file
TEMP_FILE=$(mktemp)
cp "$TESTBENCH_FILE" "$TEMP_FILE"

# Function to get the bit width from signal declaration
get_signal_width() {
    local signal_name="$1"
    local width=$(grep -E "^\s*(logic|reg|wire)\s*(\[[^\]]+\])?\s+${signal_name}\s*[;,]" "$TESTBENCH_FILE" | \
                  sed -n 's/.*\[\([^:]*\):\([^]]*\)\].*/\1/p' | head -1)
    
    if [ -z "$width" ]; then
        echo "0"  # Single bit
    else
        # Extract the left bound of the range [N:M] -> N+1 bits
        echo "$width" | sed 's/[^0-9]//g'
    fi
}

# Function to convert hex value to proper SystemVerilog literal
hex_to_sv_literal() {
    local hex_val="$1"
    local signal_name="$2"
    
    # Remove any whitespace
    hex_val=$(echo "$hex_val" | tr -d ' \t\n\r')
    
    # Get signal width
    local width=$(get_signal_width "$signal_name")
    
    # Count hex digits to determine bit width
    local hex_digits=${#hex_val}
    local bit_width=$((hex_digits * 4))
    
    # If we detected a width from signal declaration, use it
    if [ "$width" != "0" ] && [ "$width" -gt 0 ]; then
        bit_width=$((width + 1))
    fi
    
    # Format as SystemVerilog literal
    if [ "$bit_width" -eq 1 ]; then
        # Single bit - convert to binary
        case "$hex_val" in
            "0") echo "1'b0" ;;
            "1") echo "1'b1" ;;
            *) echo "1'h${hex_val}" ;;
        esac
    else
        echo "${bit_width}'h${hex_val}"
    fi
}

# Step 1: Find all input file reads and replace with hardcoded values
log_verbose "[+] Converting input file reads to hardcoded values..."

# Find all $fopen calls for input files
input_files=$(grep -o 'input_[^"]*\.hex' "$TEMP_FILE" | sort -u)

for input_file in $input_files; do
    log_verbose "  [+] Processing input file: $input_file"
    
    # Extract signal name from filename (input_SIGNAL.hex -> SIGNAL)
    signal_name=$(echo "$input_file" | sed 's/input_\(.*\)\.hex/\1/')
    
    if [ "$USE_RANDOM" = true ]; then
        # Generate random hex value
        hex_value=$(generate_random_hex "$signal_name")
        log_verbose "    [+] Generated random value: $hex_value for signal: $signal_name"
        
        # Convert to proper SystemVerilog literal
        sv_literal=$(hex_to_sv_literal "$hex_value" "$signal_name")
        log_verbose "    [+] SystemVerilog literal: $sv_literal"
        
        # Remove the entire file reading block for this input
        sed -i "/fd = \$fopen(\"$input_file\"/,/\$fclose(fd);/c\\
        // Random generated value for $signal_name\\
        $signal_name = $sv_literal;" "$TEMP_FILE"
        
    else
        # Look for the corresponding hex file in input directory
        hex_file="$INPUT_DIR/$input_file"
        
        if [ -f "$hex_file" ]; then
            # Read the hex value from file
            hex_value=$(head -1 "$hex_file" | tr -d ' \t\n\r')
            log_verbose "    [+] Found value: $hex_value for signal: $signal_name"
            
            # Convert to proper SystemVerilog literal
            sv_literal=$(hex_to_sv_literal "$hex_value" "$signal_name")
            log_verbose "    [+] SystemVerilog literal: $sv_literal"
            
            # Remove the entire file reading block for this input
            # Pattern: from $fopen to $fclose for this specific file
            sed -i "/fd = \$fopen(\"$input_file\"/,/\$fclose(fd);/c\\
            // Hardcoded value for $signal_name (from $input_file)\\
            $signal_name = $sv_literal;" "$TEMP_FILE"
            
        else
            log_verbose "    [!] Warning: Input file $hex_file not found, using default value"
            # Use a default value based on signal width
            width=$(get_signal_width "$signal_name")
            if [ "$width" == "0" ]; then
                default_val="1'b0"
            else
                default_val="${width}'h0"
            fi
            
            sed -i "/fd = \$fopen(\"$input_file\"/,/\$fclose(fd);/c\\
            // Default value for $signal_name (input file not found)\\
            $signal_name = $default_val;" "$TEMP_FILE"
        fi
    fi
done

# Step 2: Remove variable declarations that are no longer needed
log_verbose "[+] Removing unused variable declarations..."
sed -i '/string line;/d' "$TEMP_FILE"
sed -i '/int fd;/d' "$TEMP_FILE"
sed -i '/int status;/d' "$TEMP_FILE"

# Step 3: Convert output file writes to display statements
log_verbose "[+] Converting output file writes to display statements..."

# Find all output file writes
output_files=$(grep -o 'output_[^"]*\.hex' "$TEMP_FILE" | sort -u)

for output_file in $output_files; do
    log_verbose "  [+] Processing output file: $output_file"
    
    # Extract signal name from filename (output_SIGNAL.hex -> SIGNAL)
    signal_name=$(echo "$output_file" | sed 's/output_\(.*\)\.hex/\1/')
    
    # Replace the entire file writing block with a display statement
    # Pattern: from $fopen for output to $fclose
    sed -i "/fd = \$fopen(\"$output_file\"/,/\$fclose(fd);/c\\
        // Display output instead of writing to file\\
        \$display(\"$signal_name = %b (hex: %h)\", $signal_name, $signal_name);" "$TEMP_FILE"
done

# Step 4: Clean up any remaining file I/O comments
log_verbose "[+] Cleaning up comments..."
sed -i 's/\/\/ Read [0-9]* input files/\/\/ Initialize hardcoded input values/' "$TEMP_FILE"
sed -i 's/\/\/ Write [0-9]* output files/\/\/ Display output values/' "$TEMP_FILE"

# Step 5: Add a header comment explaining the conversion
log_verbose "[+] Adding header comment..."
temp_header=$(mktemp)
cat > "$temp_header" << 'EOF'
// Generated SystemVerilog testbench with hardcoded inputs
// Converted from file I/O testbench using hardcode.sh
// Original file I/O operations have been replaced with:
//   - Hardcoded input values (from input_*.hex files)
//   - Display statements for outputs (instead of output_*.hex files)

EOF

# Combine header with processed file
cat "$temp_header" "$TEMP_FILE" > "$OUTPUT_FILE"

# Clean up temp files
rm "$TEMP_FILE" "$temp_header"

# Output result to stdout, clipboard, or file
if [ "$USE_STDOUT" = true ]; then
    cat "$OUTPUT_FILE"
    rm "$OUTPUT_FILE"
elif [ "$COPY_TO_CLIPBOARD" = true ]; then
    cat "$OUTPUT_FILE" | wl-copy
    log_verbose "[+] Hardcoded testbench copied to clipboard"
    rm "$OUTPUT_FILE"
else
    log_verbose "[+] Hardcoded testbench written to: $OUTPUT_FILE"
fi

# Show a summary of what was converted
log_verbose ""
log_verbose "=== Conversion Summary ==="
if [ -n "$input_files" ]; then
    if [ "$USE_RANDOM" = true ]; then
        log_verbose "Input files converted to random hardcoded values:"
    else
        log_verbose "Input files converted to hardcoded values from test directory:"
    fi
    for input_file in $input_files; do
        signal_name=$(echo "$input_file" | sed 's/input_\(.*\)\.hex/\1/')
        if [ "$USE_RANDOM" = true ]; then
            log_verbose "  - $input_file -> random hardcoded $signal_name"
        else
            log_verbose "  - $input_file -> hardcoded $signal_name"
        fi
    done
else
    log_verbose "No input files found to convert"
fi

if [ -n "$output_files" ]; then
    log_verbose "Output files converted to display statements:"
    for output_file in $output_files; do
        signal_name=$(echo "$output_file" | sed 's/output_\(.*\)\.hex/\1/')
        log_verbose "  - $output_file -> \$display for $signal_name"
    done
else
    log_verbose "No output files found to convert"
fi

if [ "$COPY_TO_CLIPBOARD" = true ] || [ "$VERBOSE" = true ]; then
    log_verbose ""
    echo "[+] Original module `find $TESTBENCH_DIR -name '*.sv' -not -name 'testbench.sv' | sort | head -n 1`"
    echo "[+] Original testbench $TESTBENCH_FILE"
fi