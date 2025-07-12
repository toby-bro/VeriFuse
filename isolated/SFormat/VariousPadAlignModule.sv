module VariousPadAlignModule (
    input logic [7:0] in_value,
    output logic out_dummy
);
    localparam int int_data = 5;
    localparam int large_int_data = 123456;
    localparam string string_data = "abc";
    localparam string long_string_data = "longer_string";
    localparam string format_d_width = "%5d";
    localparam string format_d_zero = "%05d";
    localparam string format_d_left = "%-5d";
    localparam string format_d_left_zero = "%-05d";
    localparam string format_s_width = "%5s";
    localparam string format_s_left = "%-5s";
    string fmt_d_w;
    string fmt_d_z;
    string fmt_d_l;
    string fmt_d_lz;
    string fmt_s_w;
    string fmt_s_l;
    always_comb begin
        fmt_d_w = "";
        fmt_d_z = "";
        fmt_d_l = "";
        fmt_d_lz = "";
        fmt_s_w = "";
        fmt_s_l = "";
        if (in_value > 10) begin
            fmt_d_w = $sformatf(format_d_width, int_data);
            fmt_d_z = $sformatf(format_d_zero, int_data);
            fmt_d_l = $sformatf(format_d_left, int_data);
            fmt_d_lz = $sformatf(format_d_left_zero, int_data);
            fmt_s_w = $sformatf(format_s_width, string_data);
            fmt_s_l = $sformatf(format_s_left, string_data);
        end else begin
            fmt_d_w = $sformatf(format_d_width, in_value);
            fmt_d_z = $sformatf(format_d_zero, large_int_data);
            fmt_d_l = $sformatf(format_d_left, in_value);
            fmt_d_lz = $sformatf(format_d_left_zero, large_int_data);
            fmt_s_w = $sformatf(format_s_width, long_string_data);
            fmt_s_l = $sformatf(format_s_left, long_string_data);
        end
        out_dummy = fmt_d_w.len();
    end
endmodule

