package common_defs;
    typedef struct packed {
        logic [7:0] a;
        logic       b;
    } my_struct_t;

    int data;
    int base_val;
    int drv_val;
    logic [7:0] a;
    logic b;

endpackage

module expr_demo (
    input logic [7:0] in_a,
    input logic in_b,
    output int out_calc,
    output logic [15:0] out_concat
);
    import common_defs::*;
    always_comb begin
        out_concat = {in_a, 8'(in_b ? 8'hFF : 8'h00)};
        out_calc   = ((in_a inside {[8'd0:8'd127]}) ? int'(in_a) : -int'(in_a)) + 10;
    end
endmodule

