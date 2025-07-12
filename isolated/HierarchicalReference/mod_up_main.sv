module mod_up_level3 (
    input wire parent_up2_in,
    input wire up3_in,
    output logic up3_out
);
    assign up3_out = up3_in;
    task use_upward_ref();
        logic dummy_up_access;
        dummy_up_access = parent_up2_in;
        if (dummy_up_access) begin
        end
    endtask : use_upward_ref
    always_comb begin
        if (up3_in) begin
            use_upward_ref();
        end
    end
endmodule

module mod_up_level2 (
    input wire up2_in,
    output logic up2_out
);
    mod_up_level3 inst_up3 (.up3_in(up2_in), .parent_up2_in(up2_in), .up3_out(up2_out));
    always_comb begin
        if (up2_in) begin
        end
    end
endmodule

module mod_up_main (
    input wire up_main_in,
    output logic up_main_out
);
    mod_up_level2 inst_up2 (.up2_in(up_main_in), .up2_out(up_main_out));
    always_comb begin
        if (up_main_out) begin
        end
    end
endmodule

