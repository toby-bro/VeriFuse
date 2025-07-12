module element_select_packed (
    input logic [7:0] in_vec,
    input int index_in,
    output logic out_bit,
    output logic [3:0] out_slice
);
    always_comb begin
        if (index_in >= 0 && index_in < 8)
            out_bit = in_vec[index_in];
        else
            out_bit = 'x; 
    end
    assign out_slice = in_vec[6:3];
endmodule

