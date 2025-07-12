module ModuleInterconnectNet (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    interconnect [7:0] my_interconnect;
    logic [7:0] internal_data;
    assign internal_data = in_data;
    assign out_data = internal_data;
endmodule

