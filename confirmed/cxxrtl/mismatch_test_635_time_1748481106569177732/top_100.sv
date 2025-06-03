module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module topi (
    clkin_data,
    in_data,
    out_data,
    inj_param_out_547
);
    wire _00_;
      reg [11:0] _01_;
      reg [4:0] _02_;
      wire [6:0] _03_;
      wire celloutsig_0_0z;
      wire celloutsig_0_11z;
      wire [3:0] celloutsig_0_12z;
      wire [6:0] celloutsig_0_13z;
      wire celloutsig_0_15z;
      wire celloutsig_0_16z;
      wire celloutsig_0_17z;
      wire [5:0] celloutsig_0_19z;
      wire celloutsig_0_25z;
      wire celloutsig_0_26z;
      wire celloutsig_0_2z;
      wire celloutsig_0_3z;
      wire celloutsig_0_4z;
      wire celloutsig_0_6z;
      wire [10:0] celloutsig_0_7z;
      wire [7:0] celloutsig_0_8z;
      wire [12:0] celloutsig_0_9z;
      wire celloutsig_1_0z;
      wire celloutsig_1_10z;
      wire celloutsig_1_12z;
      wire celloutsig_1_14z;
      wire celloutsig_1_18z;
      wire celloutsig_1_19z;
      wire [3:0] celloutsig_1_1z;
      wire [5:0] celloutsig_1_2z;
      wire celloutsig_1_3z;
      wire celloutsig_1_4z;
      wire [11:0] celloutsig_1_9z;
      input [95:0] clkin_data;
      wire [95:0] clkin_data;
      input [191:0] in_data;
      wire [191:0] in_data;
      output [191:0] out_data;
      wire [191:0] out_data;
    output wire [7:0] inj_param_out_547;
    module_with_params module_with_params_inst_1000 (
    .param_in(celloutsig_0_8z),
    .param_out(inj_param_out_547)
    );
      assign celloutsig_0_15z = !(celloutsig_0_0z ? celloutsig_0_12z[1] : celloutsig_0_12z[1]);
      assign celloutsig_0_2z = !(celloutsig_0_0z ? celloutsig_0_0z : in_data[47]);
      assign celloutsig_0_11z = ~((celloutsig_0_9z[0] | in_data[8]) & celloutsig_0_7z[0]);
      assign celloutsig_1_18z = celloutsig_1_12z | ~(celloutsig_1_0z);
      assign celloutsig_1_14z = celloutsig_1_12z ^ celloutsig_1_4z;
      assign celloutsig_1_0z = in_data[144] ^ in_data[107];
      always_ff @(posedge clkin_data[0], negedge clkin_data[64])
    if (!clkin_data[64]) _02_ <= 5'h00;
    else _02_ <= { _01_[6:3], celloutsig_1_3z };
      reg [6:0] _11_;
      always_ff @(negedge celloutsig_1_19z, posedge clkin_data[32])
    if (clkin_data[32]) _11_ <= 7'h00;
    else _11_ <= { in_data[48:43], celloutsig_0_0z };
      assign { _03_[6:2], _00_, _03_[0] } = _11_;
      always_ff @(posedge clkin_data[0], posedge clkin_data[64])
    if (clkin_data[64]) _01_ <= 12'h000;
    else _01_ <= in_data[107:96];
      assign celloutsig_0_9z = { in_data[26:21], _03_[6:2], _00_, _03_[0] } / { 1'h1, celloutsig_0_7z[5:3], celloutsig_0_8z, celloutsig_0_0z };
      assign celloutsig_1_1z = { in_data[168:167], celloutsig_1_0z, celloutsig_1_0z } / { 1'h1, in_data[126:124] };
      assign celloutsig_0_13z = in_data[30:24] / { 1'h1, celloutsig_0_7z[8:4], celloutsig_0_11z };
      assign celloutsig_0_4z = { celloutsig_0_3z, celloutsig_0_2z, celloutsig_0_3z, celloutsig_0_3z, celloutsig_0_2z, celloutsig_0_0z, celloutsig_0_0z, celloutsig_0_2z, celloutsig_0_2z } === { celloutsig_0_2z, _03_[6:2], _00_, _03_[0], celloutsig_0_0z };
      assign celloutsig_1_19z = _01_[11:8] === { in_data[168:166], celloutsig_1_14z };
      assign celloutsig_0_26z = { celloutsig_0_19z[5:3], celloutsig_0_16z, celloutsig_0_17z } < celloutsig_0_8z[4:0];
      assign celloutsig_0_16z = { celloutsig_0_7z[1:0], celloutsig_0_2z } != celloutsig_0_12z[2:0];
      assign celloutsig_1_3z = { celloutsig_1_2z[2:0], celloutsig_1_0z } != in_data[174:171];
      assign celloutsig_0_7z = in_data[84:74] | { _03_[6:2], _00_, _03_[0], celloutsig_0_2z, celloutsig_0_3z, celloutsig_0_3z, celloutsig_0_2z };
      assign celloutsig_0_0z = | in_data[84:76];
      assign celloutsig_1_10z = | { _01_[10:0], celloutsig_1_4z };
      assign celloutsig_1_12z = | { celloutsig_1_9z[11:8], celloutsig_1_4z, celloutsig_1_10z, _02_ };
      assign celloutsig_0_6z = | { _03_[5:2], _00_, _03_[0], celloutsig_0_3z, celloutsig_0_4z };
      assign celloutsig_0_17z = | celloutsig_0_13z;
      assign celloutsig_1_4z = | { celloutsig_1_2z[5:3], celloutsig_1_0z };
      assign celloutsig_0_3z = | { _00_, celloutsig_0_2z, _03_[6:2], _03_[0], in_data[15:3] };
      assign celloutsig_0_25z = | { celloutsig_0_19z[1:0], _00_, celloutsig_0_15z, celloutsig_0_2z, _03_[6:2], _03_[0], in_data[15:3] };
      assign celloutsig_1_9z = { celloutsig_1_4z, celloutsig_1_1z, celloutsig_1_2z, celloutsig_1_0z } <<< in_data[130:119];
      assign celloutsig_0_12z = { celloutsig_0_7z[7:5], celloutsig_0_6z } <<< in_data[81:78];
      assign celloutsig_1_2z = { celloutsig_1_1z, celloutsig_1_0z, celloutsig_1_0z } <<< { in_data[97:96], celloutsig_1_1z };
      assign celloutsig_0_8z = { celloutsig_0_4z, _03_[6:2], _00_, _03_[0] } ~^ { _03_[5:2], _00_, _03_[0], celloutsig_0_3z, celloutsig_0_3z };
      assign celloutsig_0_19z = { celloutsig_0_13z[6:3], celloutsig_0_16z, celloutsig_0_0z } ~^ { in_data[45:41], celloutsig_0_16z };
      assign _03_[1] = _00_;
      assign { out_data[128], out_data[96], out_data[32], out_data[0] } = { celloutsig_1_18z, celloutsig_1_19z, celloutsig_0_25z, celloutsig_0_26z };
endmodule

