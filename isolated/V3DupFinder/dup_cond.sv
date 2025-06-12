module dup_cond (
    input logic [3:0] control,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result1,
    output logic [7:0] result2
);
    always_comb begin
        result1 = '0;
        result2 = '0;
        if (control[0]) begin
            result1 = data_a + data_b;
        end else begin
            result1 = data_a - data_b;
        end
        if (control[1]) begin
            result2 = data_a - data_b;
        end else begin
            result2 = data_a + data_b;
        end
        case (control[3:2])
            2'b00: result1 = data_a & data_b;
            2'b01: result1 = data_a | data_b;
            2'b10: result2 = data_a & data_b;
            2'b11: result2 = data_a | data_b;
            default: begin result1 = '0; result2 = '0; end
        endcase
        if (control[0] == control[1]) begin
            result1 = result1 + 1;
        end else if (control[2] != control[3]) begin
            result2 = result2 - 1;
        end
    end
endmodule

