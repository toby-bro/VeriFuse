module module_unpacked_array (
    input logic in1,
    input logic in2,
    output logic out1,
    output logic out2
);
    logic [1:0] data_ua[0:1] ;
    always_comb begin
        data_ua[0][0] = in1;
        data_ua[0][1] = in2;
        data_ua[1][0] = data_ua[0][0];
        data_ua[1][1] = ~data_ua[0][1];
    end
    assign out1 = data_ua[1][0];
    assign out2 = data_ua[1][1];
endmodule

