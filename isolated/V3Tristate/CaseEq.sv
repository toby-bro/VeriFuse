module CaseEq (
    inout wire [3:0] data_io,
    output wire match_z_eq,
    output wire match_x_neq
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule

