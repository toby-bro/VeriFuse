module module_unpacked_packed_struct_array (
    input logic [3:0] enable_elements_upsa,
    input logic trigger_upsa,
    output logic [3:0] status_flags_upsa
);
    typedef struct packed {
        logic flag;
        logic [2:0] value;
    } packed_element_t;
    packed_element_t elements_upsa[0:3] ;
    logic [3:0] temp_flags_upsa;
    always_comb begin
        if (trigger_upsa) begin
            if (enable_elements_upsa[0]) begin
                elements_upsa[0].flag = 1'b1;
                elements_upsa[0].value = 3'b000;
            end else begin
                elements_upsa[0].flag = 1'b0;
                elements_upsa[0].value = 3'b000;
            end
            if (enable_elements_upsa[1]) begin
                elements_upsa[1].flag = 1'b1;
                elements_upsa[1].value = 3'b001;
            end else begin
                elements_upsa[1].flag = 1'b0;
                elements_upsa[1].value = 3'b000;
            end
            if (enable_elements_upsa[2]) begin
                elements_upsa[2].flag = 1'b1;
                elements_upsa[2].value = 3'b010;
            end else begin
                elements_upsa[2].flag = 1'b0;
                elements_upsa[2].value = 3'b000;
            end
            if (enable_elements_upsa[3]) begin
                elements_upsa[3].flag = 1'b1;
                elements_upsa[3].value = 3'b011;
            end else begin
                elements_upsa[3].flag = 1'b0;
                elements_upsa[3].value = 3'b000;
            end
        end else begin
            elements_upsa[0].flag = 1'b0;
            elements_upsa[0].value = 3'b0;
            elements_upsa[1].flag = 1'b0;
            elements_upsa[1].value = 3'b0;
            elements_upsa[2].flag = 1'b0;
            elements_upsa[2].value = 3'b0;
            elements_upsa[3].flag = 1'b0;
            elements_upsa[3].value = 3'b0;
        end
        temp_flags_upsa[0] = elements_upsa[0].flag;
        temp_flags_upsa[1] = elements_upsa[1].flag;
        temp_flags_upsa[2] = elements_upsa[2].flag;
        temp_flags_upsa[3] = elements_upsa[3].flag;
    end
    assign status_flags_upsa = temp_flags_upsa;
endmodule

