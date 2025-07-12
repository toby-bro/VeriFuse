module ModuleTypes (
    input int in_val,
    input logic [7:0] packed_data,
    output int out_val,
    output bit [15:0] unpacked_data_out
);
    typedef struct packed {
        logic a;
        int   b;
    } packed_s;
    packed_s ps;
    typedef union packed {
        int i;
        int j;
    } unpacked_u;
    unpacked_u uu;
    typedef enum { IDLE, RUNNING, DONE } state_e;
    state_e current_state = IDLE;
    typedef bit [15:0] my_word_t;
    my_word_t mw;
    parameter type DATA_T = int;
    DATA_T param_var;
    always_comb begin
        ps.a = packed_data[0];
        ps.b = in_val;
        unpacked_data_out[7:0]  = packed_data;
        uu.i                    = in_val + 1;
        unpacked_data_out[15:8] = uu.j[7:0];
        out_val   = in_val + ps.b + int'(current_state);
        param_var = in_val;
        out_val   = out_val + param_var;
        mw                 = in_val;
        unpacked_data_out  = unpacked_data_out ^ mw;
    end
endmodule

