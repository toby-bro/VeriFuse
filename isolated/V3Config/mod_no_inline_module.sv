module mod_no_inline_module (
    input wire i_go,
    output logic o_done_ni
);
    logic r_toggle = 1'b0;
    always_ff @(posedge i_go) begin
        r_toggle <= ~r_toggle;
    end
    assign o_done_ni = r_toggle;
endmodule

