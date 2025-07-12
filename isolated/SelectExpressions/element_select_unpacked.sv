module element_select_unpacked (
    input int index_in,
    output logic [7:0] out_elem
);
    always_comb begin
        if (index_in >= 0 && index_in < 4)
            out_elem = in_array[index_in];
        else
            out_elem = 'x; 
    end
endmodule

