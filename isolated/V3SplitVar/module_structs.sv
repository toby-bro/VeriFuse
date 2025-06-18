module module_structs (
    input logic enable_init,
    output logic init_done_ps,
    output logic init_done_us,
    output logic [7:0] us_var_out
);
    typedef struct packed {
        logic field_a;
        logic [3:0] field_b;
    } packed_struct_t;
    typedef struct {
        logic field_c;
        logic [7:0] field_d;
    } unpacked_struct_t;
    packed_struct_t ps_var ;
    unpacked_struct_t us_var[0:1];
    logic local_init_done_ps;
    logic local_init_done_us;
    always_comb begin
        if (enable_init) begin
            ps_var.field_a = 1'b0;
            ps_var.field_b = 4'b1010;
            us_var[0].field_c = 1'b1;
            us_var[0].field_d = 8'hAA;
            us_var[1] = us_var[0];
            us_var[1].field_c = us_var[0].field_c;
            local_init_done_ps = 1'b1;
            local_init_done_us = 1'b1;
        end else begin
            ps_var = {1'b1, 4'b0101};
            us_var[0].field_c = 1'b0;
            us_var[0].field_d = 8'h00;
            us_var[1].field_c = 1'b0;
            us_var[1].field_d = 8'h00;
            local_init_done_ps = 1'b0;
            local_init_done_us = 1'b0;
        end
    end
    assign init_done_ps = local_init_done_ps;
    assign init_done_us = local_init_done_us;
    assign us_var_out = us_var[0].field_d;
endmodule

