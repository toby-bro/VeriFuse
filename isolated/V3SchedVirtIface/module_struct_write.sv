interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module module_struct_write (
    input logic [7:0] in_field1,
    input logic [7:0] in_field2,
    output logic tx_status
);
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = in_field1;
        stif_inst.packet_field2 = in_field2;
        stif_inst.tx_en = 1'b1;
        tx_status = stif_inst.tx_en;
    end
endmodule

