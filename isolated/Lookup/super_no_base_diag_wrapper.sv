class ClassNoBaseSuperDiag;
    function automatic int attempt_super();
        return 0;
    endfunction
endclass

module super_no_base_diag_wrapper (
    input int dummy_in,
    output int out_val
);
    ClassNoBaseSuperDiag instance_h;
    int local_snbdw;
    always_comb begin
        if (instance_h == null) instance_h = new();
        local_snbdw = instance_h.attempt_super();
    end
    assign out_val = local_snbdw;
endmodule

