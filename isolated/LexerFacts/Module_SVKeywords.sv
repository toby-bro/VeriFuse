module Module_SVKeywords (
    input bit [7:0] in_sv,
    output bit [7:0] out_sv
);
    assign out_sv = (in_sv inside {8'd1,8'd2,8'd3}) ? 8'hAA : 8'h55;
endmodule

