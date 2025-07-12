module PercentPercentModule (
    input logic in_bit,
    output logic out_dummy
);
    localparam string format_percent_escape = "Value: %% %d";
    localparam int data_value = 99;
    string formatted_string;
    always_comb begin
        formatted_string = "";
        if (in_bit) begin
            formatted_string = $sformatf(format_percent_escape, data_value);
        end else begin
            formatted_string = $sformatf(format_percent_escape, data_value + 1);
        end
        out_dummy = in_bit;
    end
endmodule

