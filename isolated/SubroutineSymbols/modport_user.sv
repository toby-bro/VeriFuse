interface modport_iface;
    function int calculate(input int x, input int y);
        return x - y;
    endfunction
    modport mp_imp (
        import calculate
    );
    modport mp_exp (
        export calculate
    );
endinterface
module modport_user (
    input int val1,
    input int val2,
    output int result_exp,
    output int result_imp
);
    modport_iface vif();
    always_comb begin
        result_imp = vif.mp_imp.calculate(val1, val2);
        result_exp = vif.mp_exp.calculate(val1, val2);
    end
endmodule

