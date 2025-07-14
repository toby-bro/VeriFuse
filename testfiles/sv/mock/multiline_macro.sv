module multiline_macro (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] instr,
    input  logic [6:0]  opcode
);

    // OPCODE definition
    localparam OPCODE_OP_IMM = 7'b0010011;

    // Use the multiline macro
    `ASSERT(IbexRegImmAluOpKnown, (opcode == OPCODE_OP_IMM) |->
        !$isunknown(instr[14:12]))

    // Another example
    `ASSERT(ValidOpcode, (opcode == OPCODE_OP_IMM) |-> 
        (instr[31:20] != '0))

endmodule
