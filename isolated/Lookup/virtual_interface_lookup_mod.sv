module virtual_interface_lookup_mod (
    input logic dummy_in,
    input logic [7:0] vif_data,
    input logic vif_valid,
    output logic dummy_out,
    output logic [7:0] out_data,
    output logic out_valid
);
    always_comb begin
        out_data  = vif_data;
        out_valid = vif_valid;
        dummy_out = dummy_in;
    end
endmodule

