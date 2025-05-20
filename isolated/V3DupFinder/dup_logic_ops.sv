module dup_logic_ops (
    input logic [7:0] d3,
    output logic [7:0] out1,
    input logic [3:0] flags,
    input logic [7:0] d1,
    input logic [7:0] d2
);
    logic cond1, cond2, cond3;
    logic complex_cond1, complex_cond2;
    assign cond1 = flags[0] && flags[1];
    assign cond2 = flags[2] || flags[3];
    assign cond3 = !flags[0];
    assign complex_cond1 = (cond1 || cond2) && cond3;
    assign complex_cond2 = !(flags[0] && flags[1]) || (flags[2] || !flags[3]);
    always_comb begin
        out1 = '0;
        if (complex_cond1) begin
            out1 = d1 + d2;
        end else begin
             out1 = d1 ^ d3;
        end
        if (complex_cond2) begin
             out1 = out1 + d3;
        end else begin
             out1 = out1 - d3;
        end
        if ((flags[0] && flags[1]) && (!flags[2] || flags[3])) begin
            out1 = out1 * 2;
        end
    end
endmodule

