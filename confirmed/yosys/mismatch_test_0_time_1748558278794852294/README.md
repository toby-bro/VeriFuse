
# Issue

[yosys/issue](https://github.com/YosysHQ/yosys/issues/5157)

This issue has been confirmed and was triggered by the following code:

```verilog
module stmt_if_task (
    output logic [7:0] out_val_m6,
    input logic [7:0] in_val_m6,
    input bit condition_m6
);
    logic [7:0] var_m6;
    task automatic update_conditional_m6(input bit cond, inout logic [7:0] val);
        if (cond) begin
            val++;
        end else begin
            --val;
        end
    endtask
    always_comb begin
        var_m6 = in_val_m6;
        update_conditional_m6(condition_m6, var_m6);
        out_val_m6 = var_m6;
    end
endmodule
```
