module module_packed_logic (
    input logic data_in_in_pl,
    input logic [9:0] data_in_pl,
    output logic [4:0] data_out_pl
);
    logic [15:0] my_packed_logic ;
    always_comb begin
        my_packed_logic[9:0] = data_in_pl;
        my_packed_logic[15:10] = 6'h3F;
        my_packed_logic[0] = data_in_in_pl;
    end
    assign data_out_pl[4:1] = my_packed_logic[4:1];
    assign data_out_pl[0] = my_packed_logic[1];
endmodule

