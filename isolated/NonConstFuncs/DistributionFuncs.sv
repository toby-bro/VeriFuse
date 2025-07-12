module DistributionFuncs (
    input bit dummy_input,
    input int param1_in,
    input int param2_in,
    input int param3_in,
    output int dist_chi_square_out,
    output int dist_erlang_out,
    output int dist_exponential_out,
    output int dist_normal_out,
    output int dist_poisson_out,
    output int dist_t_out,
    output int dist_uniform_out,
    output bit dummy_output
);
    always_comb begin
        $dist_uniform(dist_uniform_out, param1_in, param2_in);
        $dist_normal(dist_normal_out, param1_in, param2_in);
        $dist_exponential(dist_exponential_out, param1_in);
        $dist_poisson(dist_poisson_out, param1_in);
        $dist_chi_square(dist_chi_square_out, param1_in);
        $dist_t(dist_t_out, param1_in);
        $dist_erlang(dist_erlang_out, param1_in, param2_in);
        dummy_output = dummy_input;
    end
endmodule

