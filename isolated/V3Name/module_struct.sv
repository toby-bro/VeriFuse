module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
    typedef struct packed {
    logic [3:0] part1;
    logic [7:0] part2;
    logic [3:0] part3;
      } my_packed_struct_t;
      my_packed_struct_t unpacked_data;
      assign unpacked_data = i_packed_data;
      always @* begin
    o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
      end
endmodule

