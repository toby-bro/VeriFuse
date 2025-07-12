class MyClassLocal;
    local int local_prop = 100;
    local function automatic int get_local_prop_internal();
        return local_prop;
    endfunction
    function automatic int get_local_prop();
        return get_local_prop_internal();
    endfunction
endclass

module class_visibility_local_mod (
    input logic dummy_in,
    output int out_val
);
    MyClassLocal instance_h;
    int local_cvlm;
    always_comb begin
        if (instance_h == null) instance_h = new();
        local_cvlm = instance_h.get_local_prop();
    end
    assign out_val = local_cvlm;
endmodule

