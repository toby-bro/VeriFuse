module module_with_unconnected_drive (
    input logic in_data,
    output logic out_data_pull0,
    output logic out_data_pull1
);
    assign out_data_pull1 = in_data;
    assign out_data_pull0 = ~in_data;
endmodule

