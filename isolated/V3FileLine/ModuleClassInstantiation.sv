class MySvData;
    logic [7:0] byte_field;
    integer counter;
    function new(logic [7:0] init_byte, integer init_count);
        byte_field = init_byte;
        counter = init_count;
    endfunction
    function void increment_counter();
        counter = counter + 1;
    endfunction
endclass

module ModuleClassInstantiation (
    input logic clk,
    input int in_data,
    input logic reset,
    output int out_data
);
    MySvData my_object; 
    logic [7:0] byte_field_reg;
    integer counter_reg;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            my_object <= null; 
            byte_field_reg <= '0;
            counter_reg <= 0;
        end else begin
            if (my_object != null) begin
                byte_field_reg <= my_object.byte_field;
                counter_reg <= my_object.counter;
            end else begin
                byte_field_reg <= '0;
                counter_reg <= 0;
            end
        end
    end
    assign out_data = counter_reg + byte_field_reg;
endmodule

