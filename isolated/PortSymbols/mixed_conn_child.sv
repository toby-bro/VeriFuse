module mixed_conn_child (
    input logic [7:0] data_in,
    input logic dummy_in,
    output logic dummy_out
);
    logic dummy_internal;
    always_comb dummy_internal = |data_in | dummy_in;
    assign dummy_out = dummy_internal;
endmodule

