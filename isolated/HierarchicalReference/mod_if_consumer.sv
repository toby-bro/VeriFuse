module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module mod_if_consumer (
    input wire clk,
    input wire rst,
    output logic [7:0] out_data,
    output logic [7:0] status_reg_out
);
    logic [7:0] status_reg;
    logic consumer_internal_inst_out;
    mod_internal_if_test consumer_internal_inst (.in_i(consumer_port.req), .out_o(consumer_internal_inst_out));
    always_comb begin
        if (consumer_port.grant) begin
            out_data = consumer_port.data;
            status_reg[7:1] = 7'h1;
        end else begin
            out_data = 8'h00;
            status_reg[7:1] = 7'h0;
        end
        consumer_port.grant = consumer_port.req;
        status_reg[0] = consumer_internal_inst_out;
        if (status_reg != 8'h0) begin end
    end
    assign status_reg_out = status_reg;
endmodule

