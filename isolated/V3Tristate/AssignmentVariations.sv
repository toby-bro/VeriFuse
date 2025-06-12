module AssignmentVariations (
    output wire [7:0] out_assign_z,
    input wire [7:0] data_in,
    input wire en
);
    wire [7:0] z_wire;
    assign z_wire = data_in;
    assign z_wire = en ? 8'bz : data_in;
    assign out_assign_z = z_wire;
endmodule

