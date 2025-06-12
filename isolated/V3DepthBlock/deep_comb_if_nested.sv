module deep_comb_if_nested (
    output logic [7:0] dcout_result,
    input wire [7:0] dcin_a,
    input wire [7:0] dcin_b,
    input wire [3:0] dc_select
);
    always_comb begin
    logic [7:0] temp_result = 8'd0;
    if (dc_select[0]) begin
        if (dc_select[1]) begin
            if (dc_select[2]) begin
                if (dc_select[3]) begin
                    temp_result = dcin_a + dcin_b;
                end else begin
                    temp_result = dcin_a - dcin_b;
                end
            end else begin
                if (dc_select[3]) begin
                    temp_result = dcin_a * dcin_b;
                end else begin
                    temp_result = dcin_a / (dcin_b == 0 ? 8'd1 : dcin_b);
                end
            end
        end else begin
            if (dc_select[2]) begin
                if (dc_select[3]) begin
                    temp_result = dcin_a & dcin_b;
                end else begin
                    temp_result = dcin_a | dcin_b;
                end
            end else begin
                if (dc_select[3]) begin
                    temp_result = dcin_a ^ dcin_b;
                end else begin
                    temp_result = ~dcin_a;
                end
            end
        end
    end else begin
        if (dc_select[1]) begin
            if (dc_select[2]) begin
                if (dc_select[3]) begin
                    temp_result = {dcin_a[6:0], dcin_b[7]};
                end else begin
                    temp_result = {dcin_b[6:0], dcin_a[7]};
                end
            end else begin
                if (dc_select[3]) begin
                    temp_result = dcin_a << dc_select[1:0];
                end else begin
                    temp_result = dcin_a >> dc_select[1:0];
                end
            end
        end else begin
            if (dc_select[2]) begin
                if (dc_select[3]) begin
                    temp_result = dcin_b << dc_select[1:0];
                end else begin
                    temp_result = dcin_b >> dc_select[1:0];
                end
            end else begin
                temp_result = 8'h55;
            end
        end
    end
    dcout_result = temp_result;
    end
endmodule

