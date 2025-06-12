module class_static_mod (
    input bit enable_i,
    input int increment_i,
    output int static_value_o
);
    class StaticClass;
        static int s_member_var = 100;
        static task s_increment(input int inc);
            s_member_var += inc;
        endtask
        static function int get_s_member_var();
            return s_member_var;
        endfunction
    endclass
    always_comb begin
        if (enable_i) begin
            StaticClass::s_increment(increment_i);
        end
    end
    assign static_value_o = StaticClass::get_s_member_var();
endmodule

