# svfuzz

The objective of this project is to create a fuzzing tool to fuzz system verilog simulators.

To do this we are trying to take valid sv code and run it as a standalone program and fuzz it's inputs and try and detect discrepancies in the output.

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
