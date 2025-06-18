module module_sensitivity_list (
    input logic clock_sl,
    input logic data_in_sl,
    input logic enable_sl,
    output logic data_split_out_sl,
    output logic state_out_sl
);
    logic state_sl;
    logic [1:0] data_split_sl ;
    always_comb begin
        @(data_in_sl or enable_sl or data_split_sl)
        state_sl = enable_sl ^ data_in_sl ^ data_split_sl[0];
    end
    always_comb begin
        data_split_sl[0] = data_in_sl & enable_sl;
        data_split_sl[1] = data_in_sl | enable_sl;
    end
    assign state_out_sl = state_sl;
    assign data_split_out_sl = data_split_sl[0];
endmodule

