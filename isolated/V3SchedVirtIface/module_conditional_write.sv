interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;

    modport CtrlStat (
        output control_reg,
        output input status_reg
    );

    logic [15:0] control_reg;
      logic [15:0] status_reg;
      modport CtrlStat (output control_reg, input status_reg);
endinterface
module module_conditional_write (
    input logic condition,
    input logic [15:0] data_in,
    output logic control_status
);
    cond_if cif_inst();
      always_comb begin
    if (condition) begin
      cif_inst.control_reg = data_in;
    end else begin
      cif_inst.control_reg = 16'h0;
    end
    control_status = (cif_inst.control_reg != 16'h0);
      end
endmodule

