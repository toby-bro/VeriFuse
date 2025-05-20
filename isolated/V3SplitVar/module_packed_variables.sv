module module_packed_variables (
    input logic [7:0] data_in_pv,
    input logic [15:0] data_in_pa,
    input logic enable_pv,
    output logic [3:0] data_out_pv,
    output logic [7:0] data_out_pa
);
    logic [31:0] data_pv ;
    logic [7:0] data_pa[0:1] ;
    always_comb begin
        if (enable_pv) begin
            data_pv[7:0] = data_in_pv;
            data_pv[15:8] = ~data_in_pv;
            data_pv[23:16] = data_pv[7:0];
            data_pv[31:24] = data_pv[15:8];
            data_pa[0] = data_in_pa[7:0];
            data_pa[1] = data_in_pa[15:8];
        end else begin
            data_pv = 32'h0;
            data_pa[0] = 8'h0;
            data_pa[1] = 8'h0;
        end
    end
    assign data_out_pv = data_pv[3:0];
    assign data_out_pa = data_pa[0];
endmodule

