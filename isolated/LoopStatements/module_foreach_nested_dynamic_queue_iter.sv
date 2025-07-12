module module_foreach_nested_dynamic_queue_iter (
    input int in_cols,
    input int in_rows,
    output int out_nested_sum
);
    int dyn_2d[][];
    int queue_of_queues[$][$];
    int nested_sum;
    always_comb begin
        nested_sum = 0;
        if (in_rows > 0 && in_rows < 5 && in_cols > 0 && in_cols < 5) begin
            dyn_2d = new[in_rows];
            for (int i = 0; i < in_rows; i++) begin
                dyn_2d[i] = new[in_cols];
                for (int j = 0; j < in_cols; j++)
                    dyn_2d[i][j] = (i * 10) + j;
            end
            foreach (dyn_2d[row_idx])
                foreach (dyn_2d[row_idx][col_idx])
                    nested_sum += dyn_2d[row_idx][col_idx];
        end
        else
            dyn_2d = new[0];
        queue_of_queues.delete();
        if (in_rows > 0 && in_rows < 5 && in_cols > 0 && in_cols < 5) begin
            for (int i = 0; i < in_rows; i++) begin
                int inner_q[$];
                for (int j = 0; j < in_cols; j++)
                    inner_q.push_back((i * 100) + j);
                queue_of_queues.push_back(inner_q);
            end
            foreach (queue_of_queues[q_idx])
                foreach (queue_of_queues[q_idx][elem_idx])
                    nested_sum += queue_of_queues[q_idx][elem_idx];
        end
    end
    assign out_nested_sum = nested_sum;
endmodule

