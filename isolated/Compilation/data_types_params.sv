module data_types_params #(
    parameter int P_INT = 10,
    parameter type P_TYPE = logic
) (
    input logic i_clk,
    input logic [7:0] i_data,
    output logic [15:0] o_result
);
    typedef enum { STATE_IDLE, STATE_RUNNING } state_e;
    typedef struct packed {
        logic [3:0] header;
        logic [1:0] type_field;
    } packet_s;
    localparam int LOCAL_WIDTH = P_INT + 5;
    logic [LOCAL_WIDTH-1:0] internal_reg;
    P_TYPE  type_param_reg;
    packet_s packet_data;
    logic [7:0] unpacked_array [0:3];
    state_e current_state, next_state;
    always_comb begin
        internal_reg    = LOCAL_WIDTH'(i_data) + P_INT;
        type_param_reg  = 1;
        packet_data     = '{header: i_data[7:4], type_field: i_data[3:2]};
        for (int i = 0; i < 4; i++) unpacked_array[i] = i_data + i;
        next_state      = (current_state == STATE_IDLE) ? STATE_RUNNING : STATE_IDLE;
        o_result        = internal_reg;
    end
    always_ff @(posedge i_clk) current_state <= next_state;
endmodule

