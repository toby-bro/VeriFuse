class MyClassComplexType;
    typedef enum { STATE_IDLE, STATE_BUSY } state_e;
    state_e current_state = STATE_IDLE;
    int data;
    function new(int init_data);
        data = init_data;
    endfunction
    function void set_busy();
        current_state = STATE_BUSY;
    endfunction
endclass

module complex_class_inst_mod (
    input int in_data,
    input logic set_busy_cmd,
    output int out_data,
    output int out_state
);
    MyClassComplexType instance_h;
    int local_ccim_data;
    int local_ccim_state;
    always_comb begin
        if (instance_h == null) instance_h = new(in_data);
        if (set_busy_cmd) instance_h.set_busy();
        local_ccim_data  = instance_h.data;
        local_ccim_state = instance_h.current_state;
    end
    assign out_data  = local_ccim_data;
    assign out_state = local_ccim_state;
endmodule

