module IntegerFormatModule #(
    parameter int DataWidth = 32
) (
    input logic [31:0] in_data,
    input bit in_signed,
    output logic [31:0] out_dummy
);
    localparam string format_d = "%d";
    localparam string format_h = "%h";
    localparam string format_b = "%b";
    localparam string format_o = "%o";
    localparam string format_width_d = "%10d";
    localparam string format_zero_pad_h = "%010h";
    localparam string format_left_justify_d = "%-10d";
    localparam string format_mixed = "Int: %d, Hex: %h, Bin: %b";
    localparam [DataWidth-1:0] data_pos = 32'd12345;
    localparam [DataWidth-1:0] data_neg = -32'sd12345;
    localparam [DataWidth-1:0] data_large = 32'hFEDCBA98;
    string formatted_d;
    string formatted_h;
    string formatted_b;
    string formatted_o;
    string formatted_width_d;
    string formatted_zero_pad_h;
    string formatted_left_justify_d;
    string formatted_mixed;
    always_comb begin
        formatted_d = "";
        formatted_h = "";
        formatted_b = "";
        formatted_o = "";
        formatted_width_d = "";
        formatted_zero_pad_h = "";
        formatted_left_justify_d = "";
        formatted_mixed = "";
        if (in_signed) begin
            formatted_d = $sformatf(format_d, data_neg);
            formatted_h = $sformatf(format_h, data_neg);
            formatted_b = $sformatf(format_b, data_neg);
            formatted_o = $sformatf(format_o, data_neg);
            formatted_width_d = $sformatf(format_width_d, data_neg);
            formatted_zero_pad_h = $sformatf(format_zero_pad_h, data_large);
            formatted_left_justify_d = $sformatf(format_left_justify_d, data_neg);
            formatted_mixed = $sformatf(format_mixed, data_neg, data_large, data_pos);
        end else begin
            formatted_d = $sformatf(format_d, data_pos);
            formatted_h = $sformatf(format_h, data_pos);
            formatted_b = $sformatf(format_b, data_pos);
            formatted_o = $sformatf(format_o, data_pos);
            formatted_width_d = $sformatf(format_width_d, data_pos);
            formatted_zero_pad_h = $sformatf(format_zero_pad_h, data_pos);
            formatted_left_justify_d = $sformatf(format_left_justify_d, data_pos);
            formatted_mixed = $sformatf(format_mixed, data_pos, data_large, data_neg);
        end
        out_dummy = DataWidth;
    end
endmodule

