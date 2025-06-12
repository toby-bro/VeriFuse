module deep_logic (
    input  [7:0] a,
    input  [7:0] b,
    input  [7:0] c,
    output [7:0] out
);
    assign out = (((a & b) | (~c)) ^ (a + b)) - (c << 2);
endmodule
module procedural_complex (
    input        sel,
    input  [15:0] in1,
    input  [15:0] in2,
    output logic [15:0] out1,
    output logic [15:0] out2
);
    logic [15:0] temp1;
    logic [15:0] temp2;
    always_comb begin
        temp1 = (in1 + in2) * 10;
        if (sel) begin
            temp2 = temp1 ^ (in1 >>> 2);
            out1 = temp2 & in2;
        end else begin
            temp2 = temp1 | (in2 <<< 3);
            out1 = temp2 + in1;
        end
        out2 = temp1 - temp2;
    end
endmodule
module func_user_defined (
    input  [15:0] data_in1,
    input  [15:0] data_in2,
    output [15:0] data_out
);
    function automatic [15:0] complex_op(input [15:0] d1, input [15:0] d2);
        logic [15:0] temp_func_res;
        temp_func_res = (d1 & d2) | (d1 ^ d2);
        return temp_func_res + d2;
    endfunction
    assign data_out = complex_op(data_in1, data_in2);
endmodule
module wide_ops_deep (
    input  [63:0] wide_a,
    input  [63:0] wide_b,
    input  [63:0] wide_c,
    output [63:0] wide_out
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule
module more_procedural (
    input  [1:0] p_mode,
    input  [31:0] p_in1,
    input  [31:0] p_in2,
    output logic [31:0] p_out
);
    always_comb begin
        case (p_mode)
            2'b00: p_out = (p_in1 + p_in2) * 2;
            2'b01: p_out = (p_in1 - p_in2) / 3; 
            2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
            default: p_out = ~(p_in1 ^ p_in2) + 1;
        endcase
    end
endmodule
