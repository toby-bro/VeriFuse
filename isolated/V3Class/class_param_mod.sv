class ParamClass #(
    parameter int WIDTH = 8
);
        logic [WIDTH-1:0] value;
        function new();
          value = '0;
        endfunction
        task set_value(input logic [WIDTH-1:0] val);
          value = val;
        endtask
        function logic [WIDTH-1:0] get_value();
          return value;
        endfunction
endclass

module class_param_mod (
    input logic [15:0] param_in,
    output logic [15:0] param_out
);
    class ParamClass #(parameter int WIDTH = 8);
    logic [WIDTH-1:0] value;
    function new();
      value = '0;
    endfunction
    task set_value(input logic [WIDTH-1:0] val);
      value = val;
    endtask
    function logic [WIDTH-1:0] get_value();
      return value;
    endfunction
      endclass
      ParamClass #(16) param_instance;
      logic [15:0] param_value;
      always_comb begin
    param_instance = new();
    param_instance.set_value(param_in);
    param_value = param_instance.get_value();
      end
      assign param_out = param_value;
endmodule

