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

- Differential fuzzing of verilog simulators and synthesizers
  - Currently verilator, yosys, yosys-slang, icarus/iverilog, sv2v
- Creates complex verilog code from simple inital verilog modules called "snippets"
- Supports the fact that all simulators and synthesizers do not support the same features (cf [comparison](https://chipsalliance.github.io/sv-tests-results/))
- Guarantees nevertheless that the created verilog code has an expected simulation chance of at least 75% (value that can be changed)

### Working on

- improving the snippets
- adding more snippets
- adding more simulators and synthesizers

## Bugs found

### High quality bugs found

- Yosys
  - [Incorrect handling of post-decrement operation in `always_comb`](https://github.com/YosysHQ/yosys/issues/5151)
  - [`read_verilog`: `inout` parameters not copied out of tasks](https://github.com/YosysHQ/yosys/issues/5157)
- yosys-slang
  - [Incorrect handling of post-decrement operation in `always_comb`](https://github.com/povik/yosys-slang/issues/161)
  - [Incorrect handling of `wor`](https://github.com/povik/yosys-slang/issues/212)

### Low quality bugs

- known design defect
  - [CXXRTL - indirect clock handling](https://github.com/YosysHQ/yosys/issues/5161)
- already found but never corrected
  - [Yosys - multiple drivers on a variable in a module change values of input ports when using `prep`](https://github.com/YosysHQ/yosys/issues/5212)
- Convention on initialisation
  - [Simulation error in always @* block ?](https://github.com/steveicarus/iverilog/issues/1254)
    This bug is interesting because icarus verilog is the only one of the free simulators to correctly handle this initialisation, but did not want to bother the other repos for the moment (if I am desperate for opening issues then so be it)
  - Is it a posedge if there is no transition from 0 to 1 but an intialisation value already at one, same for negedge (cxxrtl does not agree with the other simulators about this)

## Example usage

```bash
make build-fuzzer

# Check a file for validity
./pfuzz check-file -file isolated/V3SchedTiming/mod_automatic_task.sv 

# Score snippets for better fuzzing (optional but recommended)
./scripts/score_snippets.sh

# Fuzz a file by injecting snippets into its modules
./pfuzz fuzz -n 160 -strategy smart -file testfiles/sv/ok/sequential_logic.sv -vv

```

For detailed information about the scoring system, see [docs/SCORING.md](docs/SCORING.md).

For more details on how we decide how many modules to use and which one we pick to ensure that we have simulatable code then check the [docs/INJECTING.md](docs/INJECTING.md)

## Supported tools

### Simulators

- [verilator](https://github.com/verilator/verilator)
- [cxxrtl](https://cxxrtl.org/) (in [yosys](https://yosyshq.readthedocs.io/projects/yosys/en/latest/cmd/write_cxxrtl.html))
- [icarus iverilog](https://github.com/steveicarus/iverilog) (>= 13.0)
- [xcelium](https://www.cadence.com/ja_JP/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-simulator.html)

### Synthesizers and co

- [yosys](https://github.com/YosysHQ/yosys/)
- [sv2v](https://github.com/zachjs/sv2v) (it is not a synthesizer but I tidied it there as it has a similar behaviour)
- [vivado](https://www.amd.com/en/products/software/adaptive-socs-and-fpgas/vivado.html)

## Inject snippet - expected behavior

The objective is to inject the snippet IN the original module not to write another module.
It might be usefull to have a slice / list of all the lines of the original modules to do this, to be able to modfy lines / inject lines.

What we are interested are mostly the values of the variables that are modified IN the original module. If we find one which corresponds then we inject our module the line after the input variable has been identified. If they are many different candidates for this choose one at random.

If no variable in the module is interesting then we can see if any of the inputs or outputs of the module is of any interest, if possible select clock and reset rarely (using a random decision maker once all the interesting things have been identified)

then see if the output variables of the module we are injecting have the same type as any variable higher up in the code and if they do have the same type then assign the output to this variable. Do not rename many to the same one. If you don't find any then add it to the global outputs of the module
