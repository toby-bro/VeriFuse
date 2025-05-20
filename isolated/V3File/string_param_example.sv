module string_param_example (
    input logic dummy_in_str,
    output logic dummy_out_str
);
    parameter string MODULE_DESCRIPTION = "This is a sample module with a string parameter."; 
      assign dummy_out_str = dummy_in_str;
endmodule

