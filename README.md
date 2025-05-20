# pfuzz

The objective of this project is to create a fuzzing tool to fuzz system verilog simulators.

## Example usage

```bash
make build-fuzzer
./pfuzz -check-file -file isolated/V3SchedTiming/mod_automatic_task.sv # To check a file 
./pfuzz -n 160 -strategy smart -mutate -file testfiles/sv/ok/sequential_logic.sv -vv # To fuzz a file by injecting snippets in it's modules
```

## Inject snippet - expected behavior

The objective is to inject the snippet IN the original module not to write another module.
It might be usefull to have a slice / list of all the lines of the original modules to do this, to be able to modfy lines / inject lines.

What we are interested are mostly the values of the variables that are modified IN the original module. If we find one which corresponds then we inject our module the line after the input variable has been identified. If they are many different candidates for this choose one at random.

If no variable in the module is interesting then we can see if any of the inputs or outputs of the module is of any interest, if possible select clock and reset rarely (using a random decision maker once all the interesting things have been identified)

then see if the output variables of the module we are injecting have the same type as any variable higher up in the code and if they do have the same type then assign the output to this variable. Do not rename many to the same one. If you don't find any then add it to the global outputs of the module
