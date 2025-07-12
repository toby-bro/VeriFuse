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

