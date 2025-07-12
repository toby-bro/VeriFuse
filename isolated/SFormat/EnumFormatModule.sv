module EnumFormatModule (
    input logic [1:0] in_enum_val,
    output logic [31:0] out_dummy
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_DONE = 2'b10
    } my_enum_t;
    localparam my_enum_t const_enum_idle = STATE_IDLE;
    localparam my_enum_t const_enum_busy = STATE_BUSY;
    localparam logic [1:0] const_value_not_in_enum = 2'b11;
    localparam string format_p = "%p";
    string formatted_p_enum_idle;
    string formatted_p_enum_busy;
    string formatted_p_enum_not_in_enum;
    always_comb begin
        formatted_p_enum_idle = "";
        formatted_p_enum_busy = "";
        formatted_p_enum_not_in_enum = "";
        if (in_enum_val == STATE_IDLE) begin
            formatted_p_enum_idle = $sformatf(format_p, const_enum_idle);
            formatted_p_enum_busy = $sformatf(format_p, const_enum_busy);
            formatted_p_enum_not_in_enum = $sformatf(format_p, const_value_not_in_enum);
        end else begin
            formatted_p_enum_idle = $sformatf(format_p, const_enum_busy);
            formatted_p_enum_busy = $sformatf(format_p, const_enum_idle);
            formatted_p_enum_not_in_enum = $sformatf(format_p, const_value_not_in_enum);
        end
        out_dummy = in_enum_val;
    end
endmodule

