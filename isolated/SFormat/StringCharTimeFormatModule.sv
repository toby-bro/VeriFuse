module StringCharTimeFormatModule (
    input byte in_char,
    input string in_string,
    input int in_time,
    output logic [31:0] out_dummy
);
    localparam string data_string = "Hello, World!";
    localparam byte data_char = byte'(65);
    localparam int data_time = 123456789;
    localparam string format_s = "%s";
    localparam string format_c = "%c";
    localparam string format_t = "%t";
    localparam string format_s_width = "%20s";
    localparam string format_t_width = "%25t";
    string formatted_s;
    string formatted_c;
    string formatted_t;
    string formatted_s_width;
    string formatted_t_width;
    always_comb begin
        formatted_s = "";
        formatted_c = "";
        formatted_t = "";
        formatted_s_width = "";
        formatted_t_width = "";
        if (in_string == "test") begin
            formatted_s = $sformatf(format_s, in_string);
            formatted_c = $sformatf(format_c, in_char);
            formatted_t = $sformatf(format_t, in_time);
            formatted_s_width = $sformatf(format_s_width, in_string);
            formatted_t_width = $sformatf(format_t_width, in_time);
        end else begin
            formatted_s = $sformatf(format_s, data_string);
            formatted_c = $sformatf(format_c, data_char);
            formatted_t = $sformatf(format_t, data_time);
            formatted_s_width = $sformatf(format_s_width, data_string);
            formatted_t_width = $sformatf(format_t_width, data_time);
        end
        out_dummy = in_char;
    end
endmodule

