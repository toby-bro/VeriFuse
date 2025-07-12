module specparam_pathpulse (
    input wire i_input_a,
    input wire i_input_b,
    output logic o_output_x,
    output logic o_output_y
);
    specify
        specparam PATHPULSE$i_input_a$o_output_x = (1ps, 2ps);
        specparam PATHPULSE$i_input_b$o_output_y = (3ps, 4ps);
        (i_input_a => o_output_x) = (10ps, 10ps);
        (i_input_b => o_output_y) = (12ps, 12ps);
    endspecify
    always_comb begin
        o_output_x = i_input_a;
        o_output_y = i_input_b;
    end
endmodule

