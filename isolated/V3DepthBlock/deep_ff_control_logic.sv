module deep_ff_control_logic (
    input wire [15:0] dffcl_data_in2,
    output logic [15:0] dffcl_data_out,
    input wire dffcl_clk,
    input wire dffcl_rst_n,
    input wire [3:0] dffcl_ctrl_mode,
    input wire [15:0] dffcl_data_in1
);
    always_ff @(posedge dffcl_clk or negedge dffcl_rst_n) begin
    if (!dffcl_rst_n) begin
        dffcl_data_out <= 16'h0000;
    end else begin
        case (dffcl_ctrl_mode)
            4'd0: dffcl_data_out <= dffcl_data_in1 + dffcl_data_in2;
            4'd1: begin
                if (dffcl_data_in1 > dffcl_data_in2) begin
                    case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in1 - dffcl_data_in2;
                        2'b01: dffcl_data_out <= dffcl_data_in1 & dffcl_data_in2;
                        default: dffcl_data_out <= dffcl_data_in1 | dffcl_data_in2;
                    endcase
                end else begin
                     case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in2 - dffcl_data_in1;
                        2'b01: dffcl_data_out <= dffcl_data_in1 ^ dffcl_data_in2;
                        default: dffcl_data_out <= ~dffcl_data_in1;
                    endcase
                end
            end
            4'd2: begin
                casez (dffcl_data_in1[15:13])
                    3'b000: dffcl_data_out <= dffcl_data_in2;
                    3'b001: dffcl_data_out <= ~dffcl_data_in2;
                    3'b01?: begin
                        if (dffcl_data_in2[0]) dffcl_data_out <= dffcl_data_in1 << 1;
                        else dffcl_data_out <= dffcl_data_in1 >> 1;
                    end
                    3'b1??: begin
                        if (dffcl_ctrl_mode[0]) dffcl_data_out <= dffcl_data_in1 + 1;
                        else dffcl_data_out <= dffcl_data_in1 - 1;
                    end
                    default: dffcl_data_out <= 16'hAAAA;
                endcase
            end
            default: begin
                if (dffcl_ctrl_mode[2]) dffcl_data_out <= dffcl_data_in1;
                else dffcl_data_out <= dffcl_data_in2;
            end
        endcase
    end
    end
endmodule

