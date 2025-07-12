interface my_interface;
    logic clk;
    logic en;
    logic data;
    modport master ( output clk, output en, input  data );
    modport slave  ( input  clk, input  en, output data );
    clocking cb @(posedge clk);
        input  en;
        input  data;
    endclocking
endinterface
module ModuleInterfaces (
    input logic dummy_in,
    input logic master_clk,
    input logic master_en,
    input logic slave_data_in,
    output logic dummy_out,
    output logic slave_data_out
);
    my_interface intf();
    assign intf.clk  = master_clk;
    assign intf.en   = master_en;
    assign intf.data = slave_data_in;
    assign slave_data_out = intf.data;
    virtual my_interface vif_master;
    always_comb begin
        vif_master = intf;
        dummy_out  = vif_master.cb.en;
    end
endmodule

