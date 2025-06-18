module ShiftOperations (
    input logic [7:0] data,
    input logic [2:0] shift_val,
    output logic [7:0] left_shift_log,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_log
);
    assign left_shift_log = data << shift_val;
    assign right_shift_log = data >> shift_val;
    assign right_shift_arith = $signed(data) >>> shift_val;
endmodule

