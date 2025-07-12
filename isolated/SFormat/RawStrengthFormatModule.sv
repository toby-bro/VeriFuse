module RawStrengthFormatModule (
    input logic [31:0] in_raw_32,
    input logic [63:0] in_raw_64,
    input logic [3:0] in_strength_val,
    output logic [31:0] out_dummy
);
    localparam logic [63:0] data_raw_64 = 64'h1234567890ABCDEF;
    localparam logic [31:0] data_raw_32 = 32'hAABBCCDD;
    localparam logic [7:0] data_raw_mixed = 8'b10z1x0z1;
    localparam logic [3:0] data_strength = 4'b10xZ;
    localparam string format_u = "%u";
    localparam string format_z = "%z";
    localparam string format_v = "%v";
    string formatted_u_64;
    string formatted_u_32;
    string formatted_z_mixed;
    string formatted_v;
    always_comb begin
        formatted_u_64 = "";
        formatted_u_32 = "";
        formatted_z_mixed = "";
        formatted_v = "";
        if (in_raw_64[0]) begin
            formatted_u_64 = $sformatf(format_u, in_raw_64);
            formatted_u_32 = $sformatf(format_u, in_raw_32);
            formatted_z_mixed = $sformatf(format_z, data_raw_mixed);
            formatted_v = $sformatf(format_v, in_strength_val);
        end else begin
            formatted_u_64 = $sformatf(format_u, data_raw_64);
            formatted_u_32 = $sformatf(format_u, data_raw_32);
            formatted_z_mixed = $sformatf(format_z, data_raw_mixed);
            formatted_v = $sformatf(format_v, data_strength);
        end
        out_dummy = in_raw_32;
    end
endmodule

