module ModuleBasicDisplay (
    input wire [7:0] data_in,
    input wire enable,
    output reg [7:0] data_out
);
always @* begin
    data_out = data_in;
    if (enable) begin
        $display("ModuleBasicDisplay: data_in = %d", data_in);
        $write("ModuleBasicDisplay: data_in = %h\n", data_in);
        $displayb("Binary data_in: %b", data_in);
        $displayo("Octal data_in: %o", data_in);
        $displayh("Hex data_in: %h", data_in);
        $writeb("Binary data_in: %b\n", data_in);
        $writeo("Octal data_in: %o\n", data_in);
        $writeh("Hex data_in: %h\n", data_in);
        $display("Multiple args: %d %h %b", data_in, data_in, data_in);
    end
end
endmodule

