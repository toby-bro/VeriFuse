module enum_collision(
    output enum_type1_t val1,
    output enum_type2_t val2,
);
    import test_pkg::*;
  
    enum_type1_t val1;
    enum_type2_t val2;
  
    initial begin
        val1 = VAL_A;
        val2 = VAL_C;
        val1 = VAL_B;
        val2 = VAL_A;
    end
endmodule
