`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   wire g10 = gin[1] | (pin[1] & gin[0]);
   wire g32 = gin[3] | (pin[3] & gin[2]);
   wire p10 = pin[1] & pin[0];
   wire p32 = pin[3] & pin[2];

   assign gout = g32 | (p32 & g10);       // G3-0
   assign pout = p32 & p10;               // P3-0

   wire c1 = gin[0] | (pin[0] & cin);
   wire c2 = g10 | (p10 & cin);
   wire c3 = gin[2] | (pin[2] & c2);
   assign cout = {c3, c2, c1};

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   wire g30, p30, g74, p74;
   wire [2:0] c31, c75;

   gp4 bottom_4 (
       .gin(gin[3:0]),   // bottom 4 bits of gin to gp4's gin
       .pin(pin[3:0]),   // bottom 4 bits of pin to gp4's pin
       .cin(cin),
       .gout(g30),
       .pout(p30),
       .cout(c31)
   );
   wire c4 = g30 | (p30 & cin);

   gp4 top_4 (
       .gin(gin[7:4]),   // top 4 bits of gin to gp4's gin
       .pin(pin[7:4]),   // top 4 bits of pin to gp4's pin
       .cin(c4),
       .gout(g74),
       .pout(p74),
       .cout(c75)
   );

   assign gout = g74 | (p74 & g30);
   assign pout = p74 & p30;
   assign cout = { c75, c4, c31 };

   // bottom_4_gout = G3-0
   // bottom_4_pout = P3-0
   // bottom_3_cout = C2, C1, C0

   // top_4_gout = G7-4
   // top_4_pout = P7-4

   // wire c3 = gin[2] | (pin[2] & bottom_3_cout[2]);
   // wire c4 = bottom_4_gout | (bottom_4_pout & cin);
   // wire c5 = gin[4] | (pin[4] & c4);
   
   // wire g54 = gin[5] | (pin[5] & gin[4]);
   // wire p54 = pin[5] & pin[4];

   // wire g76 = gin[7] | (pin[7] & gin[6]);
   // wire p76 = pin[7] & pin[6];

   // wire g50 = g54 | (p54 & bottom_4_gout);
   // wire p50 = p54 & bottom_4_pout;

   // wire c6 = g50 | (p50 & cin);

   // assign gout = g76 | (p76 & g50);
   // assign pout = p76 & p50;
   // assign cout[2:0] = bottom_3_cout;
   // assign cout[6:3] = { c6, c5, c4, c3 };

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] g = a & b;
   wire [31:0] p = a | b;

   // wire g70, p70;
   // wire [7:0] c71;
   // gp8 get70 (
   //    .gin(g[7:0]),
   //    .pin(p[7:0]),
   //    .cin(cin),
   //    .gout(g70),
   //    .pout(p70),
   //    .cout(c71[6:1])
   // )
   // c8 = g70 | (p70 & c0)

   wire [3:0] gr;
   wire [3:0] pr;

   // the error checker didn't like the for loop we wrote, so we
   // are manually unrolling the for loop and using names for
   // parts of what used to be c[32:0]
   // Define the separate wires
   // Define the separate wires
   wire c0, c8, c16, c24, c32;
   wire [6:0] c7_1, c15_9, c23_17, c31_25;

   assign c0 = cin;

   // First block for i = 0
   gp8 gp8_part_0 (
      .gin(g[7:0]),
      .pin(p[7:0]),
      .cin(c0),
      .gout(gr[0]),
      .pout(pr[0]),
      .cout(c7_1)
   );
   assign c8 = gr[0] | (pr[0] & c0);

   // Second block for i = 1
   gp8 gp8_part_1 (
      .gin(g[15:8]),
      .pin(p[15:8]),
      .cin(c8),
      .gout(gr[1]),
      .pout(pr[1]),
      .cout(c15_9)
   );
   assign c16 = gr[1] | (pr[1] & c8);

   // Third block for i = 2
   gp8 gp8_part_2 (
      .gin(g[23:16]),
      .pin(p[23:16]),
      .cin(c16),
      .gout(gr[2]),
      .pout(pr[2]),
      .cout(c23_17)
   );
   assign c24 = gr[2] | (pr[2] & c16);

   // Fourth block for i = 3
   gp8 gp8_part_3 (
      .gin(g[31:24]),
      .pin(p[31:24]),
      .cin(c24),
      .gout(gr[3]),
      .pout(pr[3]),
      .cout(c31_25)
   );
   assign c32 = gr[3] | (pr[3] & c24);

   // Compute sum
   wire [31:0] c = {c31_25, c24, c23_17, c16, c15_9, c8, c7_1, c0};
   assign sum = a ^ b ^ c[31:0];

endmodule
