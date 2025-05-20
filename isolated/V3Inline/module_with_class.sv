class SimpleClass;
        logic [7:0] internal_data;
        function new();
            internal_data = 8'h0;
        endfunction
        function void set_data(logic [7:0] val);
            internal_data = val;
        endfunction
        function logic [7:0] get_data();
            return internal_data;
        endfunction
endclass

module module_with_class (
    input logic reset,
    input logic [7:0] class_in,
    output logic [7:0] class_out,
    input logic clk
);
    SimpleClass my_object;
    logic [7:0] stored_data;
    initial begin
        my_object = new();
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stored_data <= 8'h0;
        end else begin
            my_object.set_data(class_in);
            stored_data <= my_object.get_data();
        end
    end
    assign class_out = stored_data;
endmodule

