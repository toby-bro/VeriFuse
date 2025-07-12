module procedural_deassign_mod (
    input logic action_select,
    input logic [7:0] value_in,
    output logic [7:0] data_out
);
    reg [7:0] my_var_reg;
    wire [7:0] my_var_wire;
    always @* begin
        if (action_select == 0) begin 
            my_var_reg = value_in;
        end else if (action_select == 1) begin 
            deassign my_var_reg;
        end else begin 
            release my_var_wire;
        end
        data_out = my_var_reg; 
    end
endmodule

