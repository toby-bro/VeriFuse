class Qualified;
    static int s_count = 100;
    local int l_val  = 20;
    protected int p_val = 30;
    const int C_VAL = 40;
    rand int r_val;
    randc int rc_val;
    function new();
        r_val = 0;
        rc_val = 0;
    endfunction
    function int get_l_val();
        return l_val;
    endfunction
    function int get_p_val();
        return p_val;
    endfunction
    function int get_c_val();
        return C_VAL;
    endfunction
    constraint c_r_val  { r_val  inside {[0:99]}; }
    constraint c_rc_val { rc_val inside {[0:9]};  }
    function void pre_randomize();
    endfunction
    function void post_randomize();
    endfunction
    function void set_rand_mode(bit on_ff);
        this.rand_mode(on_ff);
    endfunction
    function void use_srandom(int seed);
        this.srandom(seed);
    endfunction
endclass

module class_qualified_properties (
    input logic clk,
    input logic go,
    input bit rand_mode_on,
    input logic reset,
    input int srandom_seed,
    output logic [31:0] const_out,
    output logic [31:0] local_out,
    output logic [31:0] protected_out,
    output logic [31:0] rand_out,
    output logic [31:0] randc_out,
    output logic [31:0] static_out
);
    Qualified qualified_inst;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            qualified_inst   = null;
            rand_out         <= 0;
            randc_out        <= 0;
            static_out       <= 0;
            const_out        <= 0;
            local_out        <= 0;
            protected_out    <= 0;
        end else begin
            if (qualified_inst == null)
                qualified_inst = new();
            static_out    <= Qualified::s_count;
            const_out     <= qualified_inst.get_c_val();
            local_out     <= qualified_inst.get_l_val();
            protected_out <= qualified_inst.get_p_val();
            if (go) begin
                qualified_inst.set_rand_mode(rand_mode_on);
                qualified_inst.use_srandom(srandom_seed);
            end
            rand_out  <= qualified_inst.r_val;
            randc_out <= qualified_inst.rc_val;
        end
    end
endmodule

