module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module TopConfigExample (
    input bit in_tc,
    output bit out_tc
);
    Module_ConfigKeywords i_cfg (.cfg_in(in_tc), .cfg_out(out_tc));
endmodule

