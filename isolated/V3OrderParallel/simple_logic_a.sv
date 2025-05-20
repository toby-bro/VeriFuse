module simple_logic_a (
    input wire data_a,
    output wire data_b
);
    assign data_b = ~data_a;
endmodule

