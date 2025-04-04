# pfuzz

The objective of this project is to create a fuzzing tool to fuzz system verilog simulators.

To do this we are trying to take valid sv code and run it as a standalone program and fuzz it's inputs and try and detect discrepancies in the output.

## Example usage

```bash
make
```

- Change the name of the file in the `Makefile` in the `run` to the file you want as base for the fuzzing.
- To remove the verbose remove the -v flag in the `Makefile`.
- To see stats on the discrepancies run `./patterns`.
- The rest of the Makefile is self explanatory.

## What this does

pfuzz is a differential fuzzer for SystemVerilog modules that compares the behavior between different simulators (currently IVerilog and Verilator). Its core functionality includes:

1. **Automated Mocking**: Taking a SystemVerilog module with dependencies (imports, enums, etc.) and automatically generating a standalone version by mocking required components.

2. **Generating Testbenches**: Creating SystemVerilog and C++ testbenches to run simulations with both simulators.

3. **Fuzzing Strategies**: Implements multiple fuzzing strategies:

   - Simple: Basic random value generation
   - Random: Smarter random generation with special values
   - Smart: Context-aware fuzzing that recognizes signal types (clocks, resets, valid signals)

4. **Parallel Execution**: Leveraging multiple CPU cores for faster fuzzing with worker threads.

5. **Discrepancy Detection**: Finding and analyzing cases where different simulators produce different results.

6. **Result Analysis**: Tools to analyze and categorize detected mismatches using pattern recognition.

The workflow is:

1. Parse a SystemVerilog module
2. Mock dependencies and create testbenches
3. Generate test inputs using selected strategy
4. Run both simulators with identical inputs
5. Compare outputs to find discrepancies
6. Store and analyze mismatches

## Architecture

The tool is organized in several components:

- **Analyzer**: Handles parsing and mocking of SystemVerilog files
- **Fuzzer**: Orchestrates the fuzzing process and manages workers
- **Simulator**: Abstracts interaction with IVerilog and Verilator
- **TestGen**: Generates testbenches for both simulators
- **Verilog**: Provides parsing and representation of modules
- **Utils**: Common utilities for file operations, logging, etc.

Separate command-line tools are provided for:

- `pfuzz`: Main fuzzing tool
- `patterns`: Find common patterns in mismatches
- `focused`: Generate specific test cases for deeper analysis _broken at the moment_
- `analyze`: Analyze a specific mismatch in detail _broken at the moment_

## Design Decisions

1. **Mock instead of Library Integration**: Rather than requiring full library integration, we mock dependencies to make modules standalone. This makes the tool more portable and easier to use across different projects.

2. **Differential Fuzzing**: We compare outputs between simulators rather than checking correctness against a specification, which allows finding bugs without formal specifications.

3. **Signal Classification**: We recognize different types of signals (clocks, resets, etc.) and handle them differently, which improves fuzzing efficiency.

4. **Worker-based Parallelism**: Each worker has dedicated simulator instances to avoid interference and maximize throughput.

5. **Hex Format Standardization**: We ensure consistent hex value formats (including leading zeros) to avoid false positives in mismatch detection.

6. **Clock Handling in Testbenches**: Clocks are specially handled with toggling in both SystemVerilog and C++ testbenches to properly exercise sequential logic.

7. **Multi-bit Value Generation**: Width-aware value generation ensures inputs match the expected bit width of each port.

## Challenges

### Imports

The first challenge is to try and resolve the imports without using the imports. We are thus going to detect these calls and mock them so as to be able to run the code without this.

List of things to mock:

- enum casts
- imported variables
- imported functions

### Unsupported constructs

- iverilog doesn't support
  - unique

### Current Limitations

- Limited handling of more complex SystemVerilog features (interfaces, UVM, etc.)
- Mock generation might not handle all possible enum cases correctly
- Focused testing requires manual analysis of results
- Limited ability to fuzz modules with complex timing requirements

## TODO

- [ ] Suuport parametrized constructs
- [ ] Repair the focused and analyze modules
- [ ] Use the example_usage to effectively test many modules
- [ ] Combine many different sv files
- [ ] Start doing coverage-based fuzzing
- [ ] I have no idea what the following means but chatgpt suggested them so I am adding them in case I understand them tomorrow :sweat_smile:
  - [ ] Add support for complex protocol sequences
  - [ ] Implement intelligent state exploration
  - [ ] Create regression test suite for the tool itself
