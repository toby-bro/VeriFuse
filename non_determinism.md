# Sources of non determinism

This list includes : undefined behaviour as well as implementation dependant choices

- `always_comb` with multiple unordered assigns
- `always_ff` with clock which does not do a complete cycle
- multiple non blocking assign
- race condition between read and end of execution
- uninit variables
- clock edge sync (rising or decreasing)
- casex/casez with overlapping cases
- Feedback loops in `always_comb`: Combinational loops may stabilize differently
- X and Z propagation
  - X and supply values strength
- division by 0
  - CXXRTL gives 1
  - icarus gives x
  - vlator gives 0
- ferror with invalid file descriptor
- use of random probability laws

