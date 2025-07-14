package test_pkg;
    // First enum definition
    typedef enum logic [1:0] {
        VAL_A = 2'b00,
        VAL_B = 2'b01
    } enum_type1_t;
  
    // Second enum definition with duplicate values
    typedef enum logic [2:0] {
        VAL_A = 3'b000,  // Error: VAL_A already defined in this scope
        VAL_C = 3'b010
    } enum_type2_t;
endpackage

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
    end
endmodule
