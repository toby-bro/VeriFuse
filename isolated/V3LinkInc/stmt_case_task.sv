module stmt_case_task (
    input logic [7:0] data_in_m7,
    input logic [1:0] selector_in_m7,
    output logic [7:0] data_out_m7,
    output logic [1:0] selector_out_m7
);
    logic [1:0] selector_var_m7;
    logic [7:0] result_m7;
    task automatic process_case_update_m7(input logic [1:0] selector, input logic [7:0] data, output logic [7:0] res, inout logic [1:0] sel_var);
        res = 0;
        case (selector)
            2'b00: begin
                res = data + 10;
                sel_var++;
            end
            2'b01: begin
                res = data + 20;
                sel_var--;
            end
            default: begin
                res = data;
            end
        endcase
    endtask
    always_comb begin
        selector_var_m7 = selector_in_m7;
        process_case_update_m7(selector_var_m7, data_in_m7, result_m7, selector_var_m7);
        data_out_m7 = result_m7;
        selector_out_m7 = selector_var_m7;
    end
endmodule

