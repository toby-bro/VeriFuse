class my_class;
    int value;
    function new();
        value = 0;
    endfunction
endclass

module mod_basic_logic (
    input logic clk,
    input logic reset,
    output wire [7:0] data_out
);
    localparam int MAX_COUNT   = 100;
    parameter   int START_VALUE = 5;
    logic [7:0] internal_reg;
    int         counter;
    real        current_temp;
    typedef enum { IDLE, RUNNING, DONE } state_e;
    state_e current_state;
    typedef struct {
        int   value;
        logic enable;
    } data_struct_t;
    data_struct_t my_data;
    my_class inst;
    assign data_out = internal_reg + START_VALUE;
    always_comb begin
        if (current_state == IDLE) begin
            my_data.enable = 1;
            current_temp = 25.0;
        end else begin
            my_data.enable = 0;
            current_temp = 75.0;
        end
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            internal_reg  <= 0;
            counter       <= 0;
            current_state <= IDLE;
        end else begin
            if (counter < MAX_COUNT) begin
                internal_reg  <= internal_reg + 1;
                counter       <= counter + 1;
                current_state <= RUNNING;
            end else begin
                internal_state_task(internal_reg);
                current_state <= DONE;
            end
        end
    end
    initial begin
        my_data.value = initial_value_func(START_VALUE);
        inst = new();
    end
    function int initial_value_func(int start);
        return start * 2;
    endfunction
    task internal_state_task(logic [7:0] current_data);
    endtask
endmodule

