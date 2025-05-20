module deep_comb_case_complex (
    input wire [3:0] dccc_mode,
    input wire [7:0] dccc_op1,
    input wire [7:0] dccc_op2,
    output logic [7:0] dccc_output_val
);
    always_comb begin
    logic [7:0] case_res = 8'd0;
    case (dccc_mode)
        4'd0: case_res = dccc_op1 & dccc_op2;
        4'd1: begin
            case ({dccc_op1[0], dccc_op2[0]})
                2'b00: case_res = dccc_op1 | dccc_op2;
                2'b01: case_res = dccc_op1 ^ dccc_op2;
                2'b10: case_res = ~dccc_op1;
                default: case_res = ~dccc_op2;
            endcase
        end
        4'd2: begin
            if (dccc_op1 > dccc_op2) begin
                casez (dccc_op1[7:6])
                    2'b00: case_res = dccc_op1 + dccc_mode;
                    2'b01: case_res = dccc_op1 - dccc_mode;
                    2'b1?: case_res = dccc_op1 * dccc_mode;
                    default: case_res = dccc_op1 % (dccc_mode == 0 ? 4'd1 : dccc_mode);
                endcase
            end else begin
                 casez (dccc_op2[7:6])
                    2'b00: case_res = dccc_op2 + dccc_mode;
                    2'b01: case_res = dccc_op2 - dccc_mode;
                    2'b1?: case_res = dccc_op2 * dccc_mode;
                    default: case_res = dccc_op2 % (dccc_mode == 0 ? 4'd1 : dccc_mode);
                endcase
            end
        end
        4'd3, 4'd4: begin
            case ({dccc_mode[0], dccc_mode[1], dccc_mode[2]})
                3'b000: case_res = dccc_op1 << dccc_mode;
                3'b001: case_res = dccc_op1 >> dccc_mode;
                3'b010: case_res = dccc_op2 << dccc_mode;
                3'b011: case_res = dccc_op2 >> dccc_mode;
                default: begin
                    if (dccc_op1[3]) case_res = dccc_op1;
                    else case_res = dccc_op2;
                end
            endcase
        end
        default: case_res = dccc_op1 ^ dccc_op2;
    endcase
    dccc_output_val = case_res;
    end
endmodule

