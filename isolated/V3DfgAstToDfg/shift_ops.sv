module shift_ops (
    output logic [7:0] right_shift_arith,
    input logic [7:0] data,
    input logic [2:0] shamt,
    output logic [7:0] left_shift,
    output logic [7:0] right_shift_logic
);
    assign left_shift = data << shamt;
    assign right_shift_logic = data >> shamt;
    assign right_shift_arith = data >>> shamt;
endmodule

