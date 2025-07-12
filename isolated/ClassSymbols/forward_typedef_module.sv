typedef class ForwardDeclaredClass;
class ForwardDeclaredClass;
    int value;
    function new(int v);
        value = v;
    endfunction
endclass

module forward_typedef_module (
    input logic en,
    input int value_in,
    output logic [31:0] data_out
);
    ForwardDeclaredClass inst;
    always_comb begin
        if (en) begin
            inst = new(value_in);
            data_out = inst.value;
        end else begin
            inst = null;
            data_out = 0;
        end
    end
endmodule

