module ModuleGenerateIf (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val = in_val + 10;
        end else begin : bypass_block
            assign processed_val = in_val;
        end
    endgenerate
    assign out_val = processed_val;
endmodule

