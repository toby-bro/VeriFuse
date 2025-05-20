class SimpleClass;
        int member_var;
        function new();
          member_var = 0;
        endfunction
        task set_value(input int val);
          member_var = val;
        endtask
        function int get_value();
          return member_var;
        endfunction
endclass

module class_simple_mod (
    output int value_o,
    input bit clk_i,
    input int value_i
);
    class SimpleClass;
    int member_var;
    function new();
      member_var = 0;
    endfunction
    task set_value(input int val);
      member_var = val;
    endtask
    function int get_value();
      return member_var;
    endfunction
      endclass
      SimpleClass my_instance;
      int local_value;
      always_comb begin
    my_instance = new();
    my_instance.set_value(value_i);
    local_value = my_instance.get_value();
      end
      assign value_o = local_value;
endmodule

