module AssociativeArrayQueryTest (
    input int in_index_int,
    output bit dummy_out,
    output int out_high_assoc_int_idx,
    output int out_increment_assoc_int_idx,
    output int out_left_assoc_int_idx,
    output int out_low_assoc_int_idx,
    output int out_right_assoc_int_idx,
    output int out_size_assoc_int_idx
);
    int assoc_int [int];
    string assoc_str [string];
    int dummy_wire_int;
    initial begin
        assoc_int[5] = 100;
        assoc_int[1] = 200;
        assoc_int[10] = 300;
        assoc_str["apple"] = "1";
        assoc_str["banana"] = "2";
        assoc_str["cherry"] = "3";
    end
    always_comb begin
        out_low_assoc_int_idx = $low(assoc_int);
        out_high_assoc_int_idx = $high(assoc_int);
        out_left_assoc_int_idx = $left(assoc_int);
        out_right_assoc_int_idx = $right(assoc_int);
        out_size_assoc_int_idx = $size(assoc_int);
        out_increment_assoc_int_idx = $increment(assoc_int);
        dummy_wire_int = $low(assoc_int, 1);
        dummy_wire_int = $high(assoc_int, 1);
        dummy_wire_int = $left(assoc_int, 1);
        dummy_wire_int = $right(assoc_int, 1);
        dummy_wire_int = $size(assoc_int, 1);
        dummy_wire_int = $increment(assoc_int, 1);
        dummy_wire_int = $low(assoc_int, in_index_int);
        dummy_wire_int = $high(assoc_int, in_index_int);
        dummy_wire_int = $left(assoc_int, in_index_int);
        dummy_wire_int = $right(assoc_int, in_index_int);
        dummy_wire_int = $size(assoc_int, in_index_int);
        dummy_wire_int = $increment(assoc_int, in_index_int);
        dummy_out = (dummy_wire_int == 0);
    end
endmodule

