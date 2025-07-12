module FloatFormatModule (
    input real in_real,
    output logic [31:0] out_dummy
);
    localparam real data_real_pos = 123.456;
    localparam real data_real_neg = -7.89e-2;
    localparam real data_real_large = 1.23456789012345e+10;
    localparam string format_f = "%f";
    localparam string format_e = "%e";
    localparam string format_g = "%g";
    localparam string format_f_precision = "%.2f";
    localparam string format_e_width_precision = "%12.4e";
    localparam string format_g_left_justify = "%-15g";
    string formatted_f;
    string formatted_e;
    string formatted_g;
    string formatted_f_precision;
    string formatted_e_width_precision;
    string formatted_g_left_justify;
    always_comb begin
        formatted_f = "";
        formatted_e = "";
        formatted_g = "";
        formatted_f_precision = "";
        formatted_e_width_precision = "";
        formatted_g_left_justify = "";
        if (in_real > 0) begin
            formatted_f = $sformatf(format_f, data_real_pos);
            formatted_e = $sformatf(format_e, data_real_pos);
            formatted_g = $sformatf(format_g, data_real_pos);
            formatted_f_precision = $sformatf(format_f_precision, data_real_pos);
            formatted_e_width_precision = $sformatf(format_e_width_precision, data_real_pos);
            formatted_g_left_justify = $sformatf(format_g_left_justify, data_real_pos);
        end else begin
            formatted_f = $sformatf(format_f, data_real_neg);
            formatted_e = $sformatf(format_e, data_real_neg);
            formatted_g = $sformatf(format_g, data_real_neg);
            formatted_f_precision = $sformatf(format_f_precision, data_real_large);
            formatted_e_width_precision = $sformatf(format_e_width_precision, data_real_large);
            formatted_g_left_justify = $sformatf(format_g_left_justify, data_real_large);
        end
        out_dummy = $realtobits(in_real);
    end
endmodule

