module deep_function_logic (
    input wire [3:0] dfl_op_mode,
    output logic [15:0] dfl_output_res,
    input wire [15:0] dfl_input1,
    input wire [15:0] dfl_input2
);
    function automatic [15:0] complex_op (input [15:0] val1, input [15:0] val2, input [3:0] mode);
    logic [15:0] func_temp;
    func_temp = 16'h0000;
    if (mode[0]) begin
        if (mode[1]) begin
            if (mode[2]) begin
                if (mode[3]) func_temp = val1 + val2;
                else func_temp = val1 - val2;
            end else begin
                if (mode[3]) func_temp = val1 & val2;
                else func_temp = val1 | val2;
            end
        end else begin
            if (mode[2]) begin
                 if (mode[3]) func_temp = val1 ^ val2;
                 else func_temp = ~val1;
            end else begin
                 if (mode[3]) func_temp = val1 << mode[1:0];
                 else func_temp = val1 >> mode[1:0];
            end
        end
    end else begin
        if (mode[1]) begin
            case (mode[3:2])
                2'b00: func_temp = val2 + 5;
                2'b01: func_temp = val2 - 5;
                2'b10: func_temp = val2 * 2;
                default: func_temp = val2 / (val1 == 0 ? 16'd1 : val1);
            endcase
        end else begin
             if (mode[2]) func_temp = {val1[7:0], val2[7:0]};
             else func_temp = {val2[7:0], val1[7:0]};
        end
    end
    return func_temp;
    endfunction
    always_comb begin
    dfl_output_res = complex_op(dfl_input1, dfl_input2, dfl_op_mode);
    end
endmodule

