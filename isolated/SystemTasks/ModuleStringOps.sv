module ModuleStringOps (
    input wire [7:0] data_in_string,
    input wire enable_string,
    output string output_string
);
string format_string;
always @* begin
    output_string = "";
    format_string = "";
    if (enable_string) begin
        $swrite(output_string, "Data in string: %0d", data_in_string);
        $swriteb(output_string, " Data bin: %b", data_in_string);
        $swriteo(output_string, " Data oct: %o", data_in_string);
        $swriteh(output_string, " Data hex: %h", data_in_string);
        $sformat(format_string, "Formatted data: %b", data_in_string);
        $sformat(format_string, "Formatted data: %s %h", "Value", data_in_string);
        output_string = {output_string, " ", format_string};
    end
end
endmodule

