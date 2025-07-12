module ErrorTriggerModule (
    input bit in_select,
    output logic out_dummy
);
    localparam string format_missing_specifier = "Value: %";
    localparam string format_invalid_width = "%w0d";
    localparam string format_invalid_precision = "%.xd";
    localparam string format_width_not_allowed_c = "%10c";
    localparam string format_precision_not_float_d = "%.2d";
    localparam string format_zeropad_not_allowed_s = "%015s";
    localparam string format_unknown_specifier_k = "%k";
    localparam string format_unknown_specifier_A = "%A";
    localparam string format_unknown_specifier_l = "%l";
    localparam string format_unknown_specifier_m = "%m";
    localparam int data_int = 100;
    localparam byte data_byte = byte'(65);
    localparam real data_real = 5.67;
    localparam string data_string = "test";
    localparam logic [3:0] data_strength = 4'b1010;
    string fmt_err1;
    string fmt_err2;
    string fmt_err3;
    string fmt_err4;
    string fmt_err5;
    string fmt_err6;
    string fmt_err7;
    string fmt_err8;
    string fmt_err9;
    string fmt_err10;
    always_comb begin
        fmt_err1 = "";
        fmt_err2 = "";
        fmt_err3 = "";
        fmt_err4 = "";
        fmt_err5 = "";
        fmt_err6 = "";
        fmt_err7 = "";
        fmt_err8 = "";
        fmt_err9 = "";
        fmt_err10 = "";
        if (in_select) begin
            fmt_err1 = $sformatf(format_missing_specifier, data_int);
            fmt_err2 = $sformatf(format_invalid_width, data_int);
            fmt_err3 = $sformatf(format_invalid_precision, data_int);
            fmt_err4 = $sformatf(format_width_not_allowed_c, data_byte);
            fmt_err5 = $sformatf(format_precision_not_float_d, data_int);
            fmt_err6 = $sformatf(format_zeropad_not_allowed_s, data_string);
            fmt_err7 = $sformatf(format_unknown_specifier_k, data_int);
            fmt_err8 = $sformatf(format_unknown_specifier_A, data_real);
            fmt_err9 = $sformatf(format_unknown_specifier_l, data_strength);
            fmt_err10 = $sformatf(format_unknown_specifier_m, data_string);
        end else begin
            fmt_err1 = $sformatf("%d", data_int);
            fmt_err2 = $sformatf("%d", data_int);
            fmt_err3 = $sformatf("%d", data_int);
            fmt_err4 = $sformatf("%c", data_byte);
            fmt_err5 = $sformatf("%f", data_real);
            fmt_err6 = $sformatf("%s", data_string);
            fmt_err7 = $sformatf("%d", data_int);
            fmt_err8 = $sformatf("%f", data_real);
            fmt_err9 = $sformatf("%v", data_strength);
            fmt_err10 = $sformatf("%s", data_string);
        end
        out_dummy = in_select;
    end
endmodule

