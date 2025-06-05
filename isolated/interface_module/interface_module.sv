interface simple_bus;
    logic [7:0] data;
    logic valid;
    logic ready;

    modport master (
        output data,
        output valid,
        input ready
    );

    modport slave (
        input data,
        input valid,
        output ready
    );

    logic [7:0] data;
        logic valid;
        logic ready;
        modport master (
            output data, valid,
            input ready
        );
        modport slave (
            input data, valid,
            output ready
        );
endinterface
module interface_module (
    input logic clk,
    input logic rst_n,
    simple_bus.slave in_bus,
    simple_bus.master out_bus
);
    logic [7:0] stored_data;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            stored_data <= 8'h00;
            out_bus.valid <= 1'b0;
            in_bus.ready <= 1'b1;
        end else begin
            if (in_bus.valid && in_bus.ready) begin
                stored_data <= in_bus.data;
                out_bus.valid <= 1'b1;
            end
            if (out_bus.valid && out_bus.ready) begin
                out_bus.valid <= 1'b0;
            end
        end
    end
    assign out_bus.data = stored_data;
endmodule

