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

   assign cout[0] = cin;
   assign cout[1] = gin[0] | (pin[0] & cin);
   assign cout[2] = g10 | (p10 & cin);

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here

   wire bottom_4_gout, bottom_4_pout, bottom_3_cout;
   wire top_4_gout, top_4_pout, top_3_cout;

   gp4 bottom_4 (
       .gin(gin[3:0]),   // bottom 4 bits of gin to gp4's gin
       .pin(pin[3:0]),   // bottom 4 bits of pin to gp4's pin
       .cin(cin),
       .gout(bottom_4_gout),
       .pout(bottom_4_pout),
       .cout(bottom_3_cout)
   );

   // bottom_4_gout = G3-0
   // bottom_4_pout = P3-0
   // bottom_3_cout = C2, C1, C0

   // top_4_gout = G7-4
   // top_4_pout = P7-4

   wire c3 = gin[2] | (pin[2] & bottom_3_cout[2]);
   wire c4 = bottom_4_gout | (bottom_4_pout & cin);
   wire c5 = gin[4] | (pin[4] & c4);
   
   wire g54 = gin[5] | (pin[5] & gin[4]);
   wire p54 = pin[5] & pin[4];

   wire g76 = gin[7] | (pin[7] & gin[6]);
   wire p76 = pin[7] & pin[6];

   wire g50 = g54 | (p54 & bottom_4_gout);
   wire p50 = p54 & bottom_4_pout;

   wire c6 = g50 | (p50 & cin);

   assign gout = g76 | (p76 & g50);
   assign pout = p76 & p50;
   assign cout[2:0] = bottom_3_cout;
   assign cout[6:3] = { c6, c5, c4, c3 };

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here

endmodule
