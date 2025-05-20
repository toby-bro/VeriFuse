module array_assign_unhandled (
    input logic [7:0] in,
    input logic [1:0] index,
    output logic [7:0] out
);
    logic [7:0] data_arr [0:3];
      always_comb begin
    data_arr[index] = in;
      end
      assign out = data_arr[0];
endmodule

