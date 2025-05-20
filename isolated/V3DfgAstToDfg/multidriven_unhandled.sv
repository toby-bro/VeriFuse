module multidriven_unhandled (
    output logic [7:0] out,
    input logic [7:0] in1,
    input logic [7:0] in2
);
    wire [7:0] conflict_wire;
      assign conflict_wire = in1;
      assign conflict_wire = in2;
      assign out = conflict_wire;
endmodule

