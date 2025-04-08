package operation_pkg;
    // Define an enumeration type for different operations
    typedef enum logic [2:0] {
        ADD     = 3'b000,
        SUB     = 3'b001,
        MUL     = 3'b010,
        DIV     = 3'b011,
        AND     = 3'b100,
        OR      = 3'b101,
        XOR     = 3'b110,
        INVALID = 3'b111
    } operation_t;
endpackage

module enum_cast_example (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [2:0]  op_code,
    output logic [7:0]  result
);
    
    import operation_pkg::*;
    
    operation_t current_op;
    logic [7:0] a, b;
    
    // Casting from int to enum
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_op <= ADD;
            a <= 8'd0;
            b <= 8'd0;
        end else begin
            // Cast the input op_code to the enum type
            current_op <= operation_t'(op_code);
            a <= 8'd10;
            b <= 8'd5;
        end
    end
    
    // Using the enum and casting from enum to int for debug
    always_comb begin
        case (current_op)
            ADD: result = a + b;
            SUB: result = a - b;
            MUL: result = a * b;
            DIV: result = a / b;
            AND: result = a & b;
            OR:  result = a | b;
            XOR: result = a ^ b;
            default: result = 8'd0;
        endcase
        
        // For debug purposes - casting enum to int
        // $display("Current operation: %s (code: %0d)", current_op.name(), int'(current_op));
    end
    
endmodule