module ModuleCoverage (
    input logic [7:0] coverage_data,
    output logic [7:0] out_cov
);
    property p_nonzero;
        @(posedge coverage_data[0]) $countones(coverage_data) > 0;
    endproperty
    assign out_cov = coverage_data;
endmodule

