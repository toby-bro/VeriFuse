class MyDataClass;
    logic [15:0] data;
    function new(int initial_val);
        data = initial_val;
    endfunction
endclass

module module_sv_class (
    input wire i_clk,
    input wire i_enable_create,
    output logic [15:0] o_class_data
);
    MyDataClass my_object = null;
    logic [15:0] stored_data;
    assign o_class_data = stored_data;
    always @(posedge i_clk) begin
        if (i_enable_create && my_object == null) begin
            my_object = new(123); 
        end
        if (my_object != null) begin
            stored_data <= my_object.data;
        end else begin
            stored_data <= 16'b0;
        end
    end
endmodule

