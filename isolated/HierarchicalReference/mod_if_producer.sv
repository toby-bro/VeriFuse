module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module mod_if_producer (
    input wire clk,
    input wire rst,
    output logic dummy_internal_out
);
    mod_internal_if_test producer_internal_inst (.in_i(producer_port.req), .out_o(dummy_internal_out));
    always_comb begin
        producer_port.req = rst ? 1'b0 : 1'b1;
        producer_port.addr = rst ? 8'h00 : 8'h12;
        producer_port.data = rst ? 8'h00 : 8'h34;
        if (producer_port.grant) begin
            producer_port.data = 8'hFF;
        end
        if (dummy_internal_out) begin end
    end
endmodule

