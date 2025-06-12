module case_selector (
    input logic [3:0] data3,
    output logic [3:0] data_out_case,
    input logic [1:0] sel_in,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2
);
    always_comb begin
        case (sel_in)
            2'b00: data_out_case = data0; 
            2'b01: data_out_case = data1; 
            2'b10: data_out_case = data2; 
            default: data_out_case = data3; 
        endcase
    end
endmodule

