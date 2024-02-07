/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor


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


module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);    
    wire [1023:0] divd, rem, quot;

    assign divd[31:0] = i_dividend;
    assign rem[31:0] = 32'b0;
    assign quot[31:0] = 32'b0;

    genvar i;
    for (i = 0; i < 1024 - 32; i = i+32) begin
        divu_1iter d1iter(
            .i_dividend(divd[i+31:i]), 
            .i_divisor(i_divisor), 
            .i_remainder(rem[i+31:i]), 
            .i_quotient(quot[i+31:i]), 
            .o_dividend(divd[i+63:i+32]), 
            .o_remainder(rem[i+63:i+32]), 
            .o_quotient(quot[i+63:i+32])
        );
    end
    assign o_remainder = rem[1023:992];
    assign o_quotient = quot[1023:992];

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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    wire [31:0] rem_s, rem_s2, divd_msb, quot_s;

    // Initial remainder update
    left_bitshift lbs1(.in_wire(i_remainder), .out_wire(rem_s));  // (remainder << 1)
    select_msb msb(.in_wire(i_dividend), .out_wire(divd_msb));    // (dividend >> 31) & 0x1
    assign rem_s2 = rem_s | divd_msb; // remainder = (remainder << 1) | ((dividend >> 31) & 0x1)

    // Shifting the quotient regardless
    left_bitshift lbs2(.in_wire(i_quotient), .out_wire(quot_s));  // quotient = (quotient << 1)

    // Calculate outputs dependent on (remainder < divisor)
    assign o_quotient = (rem_s2 < i_divisor) ? quot_s : quot_s | 32'b1;
    assign o_remainder = (rem_s2 < i_divisor) ? rem_s2 : rem_s2 - i_divisor;

    // Shifting the dividend output
    left_bitshift lbs3(.in_wire(i_dividend), .out_wire(o_dividend));

endmodule
