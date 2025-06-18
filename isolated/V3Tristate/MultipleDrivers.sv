module MultipleDrivers (
    input wire in1,
    input wire in2,
    input wire in3,
    output wire out_multi
);
    wire multi_driver_wire;
    assign multi_driver_wire = in1;
    assign multi_driver_wire = in2;
    assign multi_driver_wire = in3;
    assign out_multi = multi_driver_wire;
endmodule

