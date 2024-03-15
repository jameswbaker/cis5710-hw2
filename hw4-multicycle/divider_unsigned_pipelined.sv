/* James Baker and Brian Williams - bakj and bewill */

`timescale 1ns / 1ns


// helper module to implement a left bitshift by 1 bit for a 32 bit input
module left_bitshift (
    input  wire [31:0] in_wire,
    output wire [31:0] out_wire
);
  assign out_wire = {in_wire[30:0], 1'b0};
endmodule

// helper module to select the most significant bit of a 32 bit input
// aka a right bitshift by 31, with an & on 0x1
module select_msb (
    input  wire [31:0] in_wire,
    output wire [31:0] out_wire
);
  assign out_wire = {31'b0, in_wire[31]};
endmodule

// quotient = dividend / divisor
module divider_unsigned_pipelined (
    input wire clk,
    rst,
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // TODO: your code here

  // (16 * 32) + 32 wires, each for one half
  // Keeps track of all iterations of the dividend, remainder, and quotient
  wire [543:0] divd_1, rem_1, quot_1;
  wire [543:0] divd_2, rem_2, quot_2;

  // Registers divd_r, quot_r, rem_r to store intermediate results
  // We also need to keep track of the divisor from the first time
  logic [31:0] divd_r, quot_r, rem_r, divs_r;

  // Init first half of iterations
  assign divd_1[31:0] = i_dividend;
  assign rem_1[31:0]  = 32'b0;
  assign quot_1[31:0] = 32'b0;

  // First half of iterations
  genvar i;
  for (i = 0; i < 512; i = i + 32) begin
    divu_1iter d1iter (
        .i_dividend (divd_1[i+31:i]),
        .i_divisor  (i_divisor),
        .i_remainder(rem_1[i+31:i]),
        .i_quotient (quot_1[i+31:i]),
        .o_dividend (divd_1[i+63:i+32]),
        .o_remainder(rem_1[i+63:i+32]),
        .o_quotient (quot_1[i+63:i+32])
    );
  end

  // Save intermediate results to registers
  always_ff @(posedge clk) begin
    if (rst) begin
      divd_r <= 32'b0;
      quot_r <= 32'b0;
      rem_r  <= 32'b0;
      divs_r <= 32'b0;
    end else begin
      divd_r <= divd_1[543:512];
      quot_r <= quot_1[543:512];
      rem_r  <= rem_1[543:512];
      divs_r <= i_divisor;
    end
  end

  // Init second half of iterations
  // Read registers to divd_2, rem_2, quotj2
  assign divd_2[31:0] = divd_r;
  assign rem_2[31:0]  = rem_r;
  assign quot_2[31:0] = quot_r;

  // Second half of iterations
  genvar j;
  for (j = 0; j < 512; j = j + 32) begin
    divu_1iter d1iter (
        .i_dividend (divd_2[j+31:j]),
        .i_divisor  (divs_r),
        .i_remainder(rem_2[j+31:j]),
        .i_quotient (quot_2[j+31:j]),
        .o_dividend (divd_2[j+63:j+32]),
        .o_remainder(rem_2[j+63:j+32]),
        .o_quotient (quot_2[j+63:j+32])
    );
  end

  assign o_remainder = rem_2[543:512];
  assign o_quotient  = quot_2[543:512];

  // split up input wires into first 16 bits and second 16 bits
  // perform 16 iterations of divison on the first 16 bits
  // store output into o_div, o_rem, o_quot into R0, R1, R2

  // Registers to store intermediate values (after 16 iters): divd_r, rem_r, quot_r
  // wires a,b use as input to divu_1iter module
  // when clk positive edge -> store intermediate results in divd_r, rem_r, quot_r
  // performs division a/b, store result into R1, R2

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  wire [31:0] rem_s, rem_s2, divd_msb, quot_s;

  // Initial remainder update
  left_bitshift lbs1 (
      .in_wire (i_remainder),
      .out_wire(rem_s)
  );  // (remainder << 1)
  select_msb msb (
      .in_wire (i_dividend),
      .out_wire(divd_msb)
  );  // (dividend >> 31) & 0x1
  assign rem_s2 = rem_s | divd_msb;  // remainder = (remainder << 1) | ((dividend >> 31) & 0x1)

  // Shifting the quotient regardless
  left_bitshift lbs2 (
      .in_wire (i_quotient),
      .out_wire(quot_s)
  );  // quotient = (quotient << 1)

  // Calculate outputs dependent on (remainder < divisor)
  assign o_quotient  = (rem_s2 < i_divisor) ? quot_s : quot_s | 32'b1;
  assign o_remainder = (rem_s2 < i_divisor) ? rem_s2 : rem_s2 - i_divisor;

  // Shifting the dividend output
  left_bitshift lbs3 (
      .in_wire (i_dividend),
      .out_wire(o_dividend)
  );

endmodule
