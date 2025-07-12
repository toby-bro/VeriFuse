module immediate_assert_mod (
    input logic clk,
    input logic condition1,
    input logic condition2,
    output logic status_ok
);
    static logic internal_status = 1;
    task my_action_task();
        internal_status = 1;
    endtask
    task my_fail_task();
        internal_status = 0;
    endtask
    always @(posedge clk) begin
        assert (condition1 == 1) my_action_task();
        else my_fail_task();
        assume (condition2 inside {0, 1});
        cover (condition1 && condition2) my_action_task();
        assert final (condition1) my_action_task();
        else my_fail_task();
        assume final (condition2) my_action_task();
        assert #0 (condition1) my_action_task(); 
        status_ok = internal_status;
    end
endmodule

