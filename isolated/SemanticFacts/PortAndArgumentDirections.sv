module PortAndArgumentDirections (
    input logic [3:0] in_dir,
    output logic [3:0] out_dir,
    inout wire [3:0] io_dir
);
    logic [3:0] internal_io;
    assign io_dir = (in_dir > 4) ? internal_io : 4'bz;
    always_comb begin
        internal_io = in_dir + 1;
        out_dir     = internal_io;
    end
    task automatic check_ref(ref logic [3:0] data);
        data = data * 2;
    endtask
endmodule

