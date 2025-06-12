module class_initial_mod (
    input int input_seed,
    output int instance_init_val_o
);
    class InitialClass;
        int instance_var;
        function new(int seed_val);
            instance_var = seed_val;
        endfunction
        function int get_instance_var();
            return instance_var;
        endfunction
    endclass
    InitialClass inst_init;
    int local_instance_val;
    always_comb begin
        inst_init = new(input_seed);
        local_instance_val = inst_init.get_instance_var();
    end
    assign instance_init_val_o = local_instance_val;
endmodule

