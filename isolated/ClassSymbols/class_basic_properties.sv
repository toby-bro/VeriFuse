class Basic;
    int data;
    function new();
        data = 5;
    endfunction
    function int getData();
        return data;
    endfunction
endclass

module class_basic_properties (
    input logic en,
    output logic [31:0] output_data
);
    Basic basic_inst;
    always_comb begin
        if (en) begin
            basic_inst = new();
            output_data = (basic_inst != null) ? basic_inst.getData() : 0;
        end else begin
            basic_inst = null;
            output_data = 0;
        end
    end
endmodule

