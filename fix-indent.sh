#!/bin/bash

# Script to normalize indentation to multiples of 4 spaces  
# Preserves the existing indentation hierarchy and relative changes

if [ $# -eq 0 ]; then
    echo "Usage: $0 <file>"
    exit 1
fi

input_file="$1"

if [ ! -f "$input_file" ]; then
    echo "Error: File '$input_file' not found"
    exit 1
fi

# Create backup
cp "$input_file" "${input_file}.bak"

# Process the file using awk to preserve indentation hierarchy
awk '
BEGIN {
    # Array to track indent levels seen so far
    indent_levels[0] = 0  # Base level is 0
    level_count = 1
}
{
    # Handle empty lines
    if (/^[ \t]*$/) {
        print
        next
    }
    
    # Convert tabs to 4 spaces first
    gsub(/\t/, "    ")
    
    # Count leading spaces
    leading_spaces = 0
    for (i = 1; i <= length($0); i++) {
        if (substr($0, i, 1) == " ") {
            leading_spaces++
        } else {
            break
        }
    }

    # Find or assign indent level
    found_level = -1
    for (level in indent_levels) {
        if (indent_levels[level] == leading_spaces) {
            found_level = level
            break
        }
    }

    # If this is a new indent level
    if (found_level == -1) {
        # Find the appropriate level by comparing with existing levels
        target_level = 0
        for (level = 0; level < level_count; level++) {
            if (leading_spaces > indent_levels[level]) {
                target_level = level + 1
            }
        }
        
        # Shift existing levels if needed
        for (level = level_count; level > target_level; level--) {
            indent_levels[level] = indent_levels[level-1]
        }
        
        # Insert new level
        indent_levels[target_level] = leading_spaces
        level_count++
        found_level = target_level
    }

    previous_level = indent_levels[level_count - 1]
    # If this is a smaller level than the last one, delete all levels greater than this
    if (leading_spaces < previous_level) {
        for (level = level_count - 1; level >= 0; level--) {
            if (indent_levels[level] > leading_spaces) {
                delete indent_levels[level]
                level_count--
            } else {
                break
            }
        }
    }
    
    # Calculate normalized indentation (each level = 4 spaces)
    normalized_indent = found_level * 4
    
    # Get content without leading spaces
    content = substr($0, leading_spaces + 1)
    
    # Print with normalized indentation
    printf "%*s%s\n", normalized_indent, "", content
}' "$input_file" > "${input_file}.tmp"

# Replace original file
modified=$(diff "$input_file" "${input_file}.tmp")
if [ -z "$modified" ]; then
    rm "${input_file}.tmp"
    exit 0
fi
mv "${input_file}.tmp" "$input_file"

echo "Indentation fixed in $input_file (backup saved as ${input_file}.bak)"
