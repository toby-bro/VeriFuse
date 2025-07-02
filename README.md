# pfuzz

P stands for parser and not python which was the original idea and the reason for the name.
Other suggested names are:

| Name       | Votes |
| ---------- | ----- |
| pfuzz      | 0     |
| parsifuzz  | #rems     |
| parsifluzz | #flo     |
| parsifleur | 0     |

The objective of this project is to create a fuzzing tool to fuzz system verilog simulators.

## Features

- **Smart Snippet Injection**: Intelligently injects Verilog/SystemVerilog snippets into target modules
- **Weighted Snippet Selection**: Snippets are scored based on simulator/synthesizer compatibility and selected proportionally to reduce compilation failures
- **Multi-Simulator Support**: Tests against IVerilog, Verilator, CXXRTL, and other simulators
- **Synthesis Integration**: Includes Yosys and SV2V synthesis tool support
- **Mismatch Detection**: Automatically detects behavioral differences between simulators

## Example usage

```bash
make build-fuzzer

# Check a file for validity
./pfuzz check-file -file isolated/V3SchedTiming/mod_automatic_task.sv 

# Score snippets for better fuzzing (optional but recommended)
./pfuzz score-snippets -v

# Fuzz a file by injecting snippets into its modules
./pfuzz fuzz -n 160 -strategy smart -file testfiles/sv/ok/sequential_logic.sv -vv

# Alternative: use bash script for scoring
./scripts/score_snippets.sh
```

For detailed information about the scoring system, see [docs/SCORING.md](docs/SCORING.md).

## Inject snippet - expected behavior

The objective is to inject the snippet IN the original module not to write another module.
It might be usefull to have a slice / list of all the lines of the original modules to do this, to be able to modfy lines / inject lines.

What we are interested are mostly the values of the variables that are modified IN the original module. If we find one which corresponds then we inject our module the line after the input variable has been identified. If they are many different candidates for this choose one at random.

If no variable in the module is interesting then we can see if any of the inputs or outputs of the module is of any interest, if possible select clock and reset rarely (using a random decision maker once all the interesting things have been identified)

then see if the output variables of the module we are injecting have the same type as any variable higher up in the code and if they do have the same type then assign the output to this variable. Do not rename many to the same one. If you don't find any then add it to the global outputs of the module

## How to read the worker dir

### SubDirs

- `cxxrtl_sim` execution dir for vanilla yosys and cxxrtl
- `cxxrtl_slang_sim` execution dir for yosys with yosys slang and cxxrtl
- `iverilog_run` same for iverilog
- `vl_O0` same for verilator with optimisations set to 0
- `vl_O0` same for verilator with optimisations set to 3

- `test_X` is the test dir for test number X
  - `input_NAME.hex` is the input to the testbench port named NAME
  - `SIM_out_NAME.hex` is the output (in binary) for the port named NAME for the simulation with SIM

- `testbench.sv` is the sv testbench for the module we are testing (the cpp testbench can be found in the `cxxrtl_sim` dir)
- `MODULE.sv` is the file we are testing
