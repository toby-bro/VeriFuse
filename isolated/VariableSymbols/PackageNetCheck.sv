package package_with_nets;
    wire [7:0] package_net_init;
    wire [7:0] package_net_no_init;

endpackage

module PackageNetCheck (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    import package_with_nets::*;
    assign package_net_no_init = in_val;
    assign package_net_init    = in_val + 1;
    always_comb begin
        out_val = package_net_init + package_net_no_init;
    end
endmodule

