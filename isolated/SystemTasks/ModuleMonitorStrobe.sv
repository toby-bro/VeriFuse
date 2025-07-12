module ModuleMonitorStrobe (
    input wire clk_monitor,
    input wire [7:0] data_in_monitor,
    input wire enable_monitor,
    output reg [7:0] data_out_monitor
);
always @(posedge clk_monitor) begin
    data_out_monitor <= data_in_monitor;
    if (enable_monitor) begin
        $monitor("ModuleMonitorStrobe: data_in=%d data_out=%d", data_in_monitor, data_out_monitor);
        $monitorb("Monitor Binary: %b", data_in_monitor);
        $monitoro("Monitor Octal: %o", data_in_monitor);
        $monitorh("Monitor Hex: %h", data_in_monitor);
    end
end
always @* begin
    if (enable_monitor && data_in_monitor > 100) begin
        $strobe("ModuleMonitorStrobe: Strobe! data_in=%d data_out=%d", data_in_monitor, data_out_monitor);
        $strobeb("Strobe Binary: %b", data_in_monitor);
        $strobeo("Strobe Octal: %o", data_in_monitor);
        $strobeh("Strobe Hex: %h", data_in_monitor);
    end
end
endmodule

