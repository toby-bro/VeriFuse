class my_class;
    int data;
    function new(int initial_data);
        data = initial_data;
    endfunction
endclass

module ClassVariableInstantiation (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    my_class my_object;
    int      object_data;
    always_comb begin
        if (in_val != 0) begin
            my_object   = new(in_val);
            object_data = my_object.data;
        end
        else begin
            object_data = 0;
        end
        out_val = object_data;
    end
endmodule

