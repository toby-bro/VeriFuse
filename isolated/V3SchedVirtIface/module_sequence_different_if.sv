interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module module_sequence_different_if (
    input logic [31:0] input1,
    input logic [7:0] input2_byte,
    output logic sequence_valid
);
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = input1;
        sif2_port.status_byte = input2_byte;
        sequence_valid = 1'b1;
    end
endmodule

