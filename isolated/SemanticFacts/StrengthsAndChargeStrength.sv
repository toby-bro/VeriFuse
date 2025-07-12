module StrengthsAndChargeStrength (
    input wire in_data_s,
    output wire out_data_s
);
    wire (supply1, supply0) drive_wire_sup = in_data_s;
    wire (strong1, weak0)   drive_wire_sw  = in_data_s;
    wire (weak0,  strong1)  drive_wire_ws  = !in_data_s;
    wire (pull0,  weak1)    drive_wire_p0w = in_data_s;
    wire (weak0,  pull1)    drive_wire_wp1 = !in_data_s;
    wire (highz0, weak1)    drive_wire_hz0w = in_data_s;
    wire (weak0,  highz1)   drive_wire_whz1 = !in_data_s;
    wire (pull0,  pull1)    pull_wire0 = in_data_s;
    wire (pull1,  pull0)    pull_wire1 = !in_data_s;
    trireg (small)  tri_small  = in_data_s;
    trireg (medium) tri_medium = !in_data_s;
    trireg (large)  tri_large  = in_data_s | !in_data_s;
    trireg          tri_default = 1'b1;
    assign out_data_s = drive_wire_sup | drive_wire_sw | drive_wire_ws | drive_wire_p0w |
        drive_wire_wp1 | drive_wire_hz0w | drive_wire_whz1 | pull_wire0 |
        pull_wire1 | tri_medium | tri_small | tri_large | tri_default;
endmodule

