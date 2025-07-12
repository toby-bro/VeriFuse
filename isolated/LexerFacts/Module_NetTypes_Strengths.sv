typedef logic [3:0] my_custom_net_t;
module Module_NetTypes_Strengths (
    input bit drive_in,
    output wire pulldown_out,
    output wire pullup_out,
    output logic scalared_out,
    output wire tri0_out,
    output wire tri1_out,
    output wire tri_out,
    output wire triand_out,
    output wire trior_out,
    output wire trireg_out,
    output wire uwire_out,
    output wire wand_out,
    output wire wor_out
);
    uwire    my_uwire;
    tri      my_tri;
    tri0     my_tri0;
    tri1     my_tri1;
    triand   my_triand;
    trior    my_trior;
    trireg   my_trireg;
    wand     my_wand;
    wor      my_wor;
    wire     pulldown_internal;
    wire     pullup_internal;
    wire     scalar_wire;
    my_custom_net_t custom_net_internal;
    pulldown pd_drv(pulldown_internal);
    pullup   pu_drv(pullup_internal);
    assign my_uwire          = drive_in;
    assign my_tri            = drive_in;
    assign my_tri0           = drive_in;
    assign my_tri1           = drive_in;
    assign my_triand         = drive_in;
    assign my_trior          = drive_in;
    assign my_trireg         = drive_in;
    assign my_wand           = drive_in;
    assign my_wor            = drive_in;
    assign uwire_out         = my_uwire;
    assign tri_out           = my_tri;
    assign tri0_out          = my_tri0;
    assign tri1_out          = my_tri1;
    assign triand_out        = my_triand;
    assign trior_out         = my_trior;
    assign trireg_out        = my_trireg;
    assign wand_out          = my_wand;
    assign wor_out           = my_wor;
    assign pulldown_out      = pulldown_internal;
    assign pullup_out        = pullup_internal;
    assign scalar_wire       = drive_in;
    assign scalared_out      = scalar_wire;
    assign custom_net_internal = drive_in ? 4'b1111 : 4'b0000;
    assign custom_net_out      = custom_net_internal;
endmodule

