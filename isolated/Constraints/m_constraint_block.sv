module m_constraint_block (
    input bit enable_block,
    output bit block_status
);
    assign block_status = enable_block;
    class c_constraint_block;
        rand int x, y, z;
        constraint my_block { 
            x > 0; 
            y < 10;
            z == x + y;
        }
        constraint empty_block {}; 
    endclass
    c_constraint_block inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule

