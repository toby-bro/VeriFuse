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

## TODO

- [ ] Parmetrized constructs
- [ ] Repair the focused and analysed modules
- [ ] Use the example_usage to effectively test many modules
- [ ] Combine many different sv files
- [ ] Start doing coverage based fuzzing
