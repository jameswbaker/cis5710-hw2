`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

// size of the wire to track insn name (6 bits)
`define INSN_NAME_SIZE 5:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif


/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE  = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI   = 32
} cycle_status_e;

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // Reads
  assign rs1_data = regs[rs1];  // read from rs1
  assign rs2_data = regs[rs2];  // read from rs2
  assign regs[0]  = 32'd0;  // x0 is hardwired to 0

  // Writes
  // what does always_ff do? It's a clocked always block, meaning it only runs when the clock is 1
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 1; i < NumRegs; i++) begin
        regs[i] <= 32'd0;  // Reset all registers to 0, except for reg[0]
      end
    end else if (we && rd != 5'd0) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  // logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** execute state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rs1;
  logic [4:0] rs2;
  logic [4:0] rd;

  logic [19:0] imm_u;
  logic [4:0] imm_i_4_0;
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_s_sext;
  logic [`REG_SIZE] imm_j_sext;

  logic [`INSN_NAME_SIZE] insn_name;
} stage_execute_t;

/** memory state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [4:0] rs2;

  logic [`REG_SIZE] rd_data;
  logic [`REG_SIZE] rs2_data;
  logic [`REG_SIZE] divide_flip_sign;

  logic [`REG_SIZE] addr_to_dmem;

  logic [5:0] insn_name;
  logic [`REG_SIZE] divide_by_zero;
  logic is_load_insn;

  logic we;
  logic halt;
} stage_memory_t;

/** writeback state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;

  logic is_load_insn;

  logic we;
  logic halt;
} stage_writeback_t;



/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    // parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
      // start out ready to accept incoming reads
      insn.ARREADY <= 1;
      data.ARREADY <= 1;
      // start out ready to accept an incoming write
      data.AWREADY <= 1;
      data.WREADY  <= 1;

      insn.RDATA   <= 0;
      data.RDATA   <= 0;

    end else begin
      // Reading instructions
      if (insn.ARREADY == 1 && insn.ARVALID == 1) begin
        insn.RVALID <= 1;
        insn.RRESP  <= ResponseOkay;
        insn.RDATA  <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
      end else begin
        insn.RVALID <= 0;
      end

      // data read address
      if (data.ARREADY == 1 && data.ARVALID == 1) begin
        data.RVALID <= 1;
        data.RRESP  <= ResponseOkay;
        data.RDATA  <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
      end else begin
        data.RVALID <= 0;
      end

      // data write address
      if (data.AWVALID && data.AWREADY && data.WVALID && data.WREADY && data.BREADY) begin
        data.BVALID <= 1;
        data.BRESP  <= ResponseOkay;

        // using strobe, we should only write to the bytes that have been specified
        if (data.WSTRB[0]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
        end
        if (data.WSTRB[1]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
        end
        if (data.WSTRB[2]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
        end
        if (data.WSTRB[3]) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
        end

        // mem_array[data.AWADDR[AddrMsb:AddrLsb]] <= data.WDATA;
      end else begin
        insn.BVALID <= 0;
      end
    end
  end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
endmodule


module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    /*

    pc_to_imem
    imem.
    */

    // Start by replacing this interface to imem...
    // output logic [ `REG_SIZE] pc_to_imem,
    // input  wire  [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // pc_to_imem (output) -> imem.ARADDR
    // insn_from_imem (input) -> imem.RDATA

    // Once imem is working, replace this interface to dmem...
    // output logic [`REG_SIZE] addr_to_dmem,
    // input wire [`REG_SIZE] load_data_from_dmem,
    // output logic [`REG_SIZE] store_data_to_dmem,
    // output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    axi_if.manager dmem,

    // addr_to_dmem (output) -> 

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  /***********/
  /* MODULES */
  /***********/

  // The insn in the execute stage is READING from
  // the register file, while the insn in the writeback stage
  // is WRITING to the register file
  RegFile rf (
      .rd(writeback_state.rd),
      .rd_data(w_rd_data),
      .rs1(execute_state.rs1),
      .rs1_data(x_rs1_data),
      .rs2(execute_state.rs2),
      .rs2_data(x_rs2_data),

      .clk(clk),
      .we (w_we),
      .rst(rst)
  );

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  // DON'T TOUCH THIS
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  logic [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (x_branching) begin
      f_pc_current   <= x_branch_pc;
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (x_load_stall || x_divide_to_use_stall || d_fence_stall) begin
      f_pc_current   <= f_pc_current;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_pc_current   <= f_pc_current + 4;
      f_cycle_status <= CYCLE_NO_STALL;
    end
  end

  always_comb begin
    imem.ARVALID = 1;
    imem.RREADY  = 1;
    imem.ARADDR  = f_pc_current;
  end

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  // wire [255:0] f_disasm;
  // Disasm #(
  //     .PREFIX("F")
  // ) disasm_0fetch (
  //     .insn  (f_insn),
  //     .disasm(f_disasm)
  // );

  /****************/
  /* DECODE STAGE */
  /****************/

  logic [`REG_SIZE] d_insn_curr;
  logic [`REG_SIZE] d_insn_prev;  // for saving the prev insn state
  logic [`REG_SIZE] d_insn;  // the actual insn we will end up using (after stalling)

  always_comb begin
    if (decode_state.cycle_status == CYCLE_TAKEN_BRANCH) begin
      d_insn_curr = 0;
    end else begin
      d_insn_curr = imem.RDATA;
    end
  end

  // this is the actual d_insn we should use
  always_comb begin
    if (execute_state.cycle_status == CYCLE_LOAD2USE) begin
      d_insn = d_insn_prev;
    end else begin
      d_insn = d_insn_curr;
    end
  end

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    d_insn_prev <= d_insn_curr;

    if (rst) begin
      decode_state <= '{pc: 0, cycle_status: CYCLE_RESET};
    end else if (x_branching) begin
      decode_state <= '{pc: 0, cycle_status: CYCLE_TAKEN_BRANCH};
    end else if (x_load_stall || x_divide_to_use_stall || d_fence_stall) begin
      decode_state <= '{pc: decode_state.pc, cycle_status: CYCLE_NO_STALL};
    end else begin
      begin
        decode_state <= '{pc: f_pc_current, cycle_status: f_cycle_status};
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (d_insn),
      .disasm(d_disasm)
  );

  // components of the instruction
  wire [6:0] d_insn_funct7;
  wire [2:0] d_insn_funct3;
  wire [4:0] d_insn_rs1;
  wire [4:0] d_insn_rs2;
  wire [4:0] d_insn_rd;
  wire [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = d_insn;

  // set rs1 and rs2 to zero if unused; this is for checking specific conditions later (where we ignore
  // rs1 and rs2 if they are zero)
  // - example reason we have to do this: in checking for load-use stalls, we look at if the decode rs2 and execute rd
  //   are the same, but there may be cases where rs2 is accidentally set when it isn't actually used
  logic [4:0] d_insn_rs1_fixed;
  logic [4:0] d_insn_rs2_fixed;
  always_comb begin
    if (d_insn_opcode == OpLui) begin
      d_insn_rs1_fixed = 0;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpAuipc) begin
      d_insn_rs1_fixed = 0;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpJal) begin
      d_insn_rs1_fixed = 0;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpMiscMem) begin
      d_insn_rs1_fixed = 0;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpEnviron) begin
      d_insn_rs1_fixed = 0;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpJalr) begin
      d_insn_rs1_fixed = d_insn_rs1;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpLoad) begin
      d_insn_rs1_fixed = d_insn_rs1;
      d_insn_rs2_fixed = 0;
    end else if (d_insn_opcode == OpRegImm) begin
      d_insn_rs1_fixed = d_insn_rs1;
      d_insn_rs2_fixed = 0;
    end else begin
      d_insn_rs1_fixed = d_insn_rs1;
      d_insn_rs2_fixed = d_insn_rs2;
    end
  end

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] d_imm_i;
  assign d_imm_i = d_insn[31:20];
  wire [ 4:0] d_imm_shamt = d_insn[24:20];
  wire [ 4:0] d_imm_i_4_0 = d_imm_i[4:0];

  // S - stores
  wire [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd;

  // B - conditionals
  wire [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7,
      {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd,
      d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {
    d_insn[31:12], 1'b0
  };

  // U - setup for U type instructions
  wire [19:0] d_imm_u;
  assign d_imm_u = d_insn[31:12];

  wire [`REG_SIZE] d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  wire [`REG_SIZE] d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  wire [`REG_SIZE] d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  wire [`REG_SIZE] d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire d_insn_lui = d_insn_opcode == OpLui;
  wire d_insn_auipc = d_insn_opcode == OpAuipc;
  wire d_insn_jal = d_insn_opcode == OpJal;
  wire d_insn_jalr = d_insn_opcode == OpJalr;

  wire d_insn_beq = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b000;
  wire d_insn_bne = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b001;
  wire d_insn_blt = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b100;
  wire d_insn_bge = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b101;
  wire d_insn_bltu = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b110;
  wire d_insn_bgeu = d_insn_opcode == OpBranch && d_insn[14:12] == 3'b111;

  wire d_insn_lb = d_insn_opcode == OpLoad && d_insn[14:12] == 3'b000;
  wire d_insn_lh = d_insn_opcode == OpLoad && d_insn[14:12] == 3'b001;
  wire d_insn_lw = d_insn_opcode == OpLoad && d_insn[14:12] == 3'b010;
  wire d_insn_lbu = d_insn_opcode == OpLoad && d_insn[14:12] == 3'b100;
  wire d_insn_lhu = d_insn_opcode == OpLoad && d_insn[14:12] == 3'b101;

  wire d_insn_sb = d_insn_opcode == OpStore && d_insn[14:12] == 3'b000;
  wire d_insn_sh = d_insn_opcode == OpStore && d_insn[14:12] == 3'b001;
  wire d_insn_sw = d_insn_opcode == OpStore && d_insn[14:12] == 3'b010;

  wire d_insn_addi = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b000;
  wire d_insn_slti = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b010;
  wire d_insn_sltiu = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b011;
  wire d_insn_xori = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b100;
  wire d_insn_ori = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b110;
  wire d_insn_andi = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b111;

  wire d_insn_slli = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b001 && d_insn[31:25] == 7'd0;
  wire d_insn_srli = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b101 && d_insn[31:25] == 7'd0;
  wire d_insn_srai = d_insn_opcode == OpRegImm && d_insn[14:12] == 3'b101 && d_insn[31:25] == 7'b0100000;

  wire d_insn_add = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b000 && d_insn[31:25] == 7'd0;
  wire d_insn_sub  = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b000 && d_insn[31:25] == 7'b0100000;
  wire d_insn_sll = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b001 && d_insn[31:25] == 7'd0;
  wire d_insn_slt = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b010 && d_insn[31:25] == 7'd0;
  wire d_insn_sltu = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b011 && d_insn[31:25] == 7'd0;
  wire d_insn_xor = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b100 && d_insn[31:25] == 7'd0;
  wire d_insn_srl = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b101 && d_insn[31:25] == 7'd0;
  wire d_insn_sra  = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b101 && d_insn[31:25] == 7'b0100000;
  wire d_insn_or = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b110 && d_insn[31:25] == 7'd0;
  wire d_insn_and = d_insn_opcode == OpRegReg && d_insn[14:12] == 3'b111 && d_insn[31:25] == 7'd0;

  wire d_insn_mul = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b000;
  wire d_insn_mulh = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b001;
  wire d_insn_mulhsu = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b010;
  wire d_insn_mulhu = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b011;
  wire d_insn_div = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b100;
  wire d_insn_divu = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b101;
  wire d_insn_rem = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b110;
  wire d_insn_remu = d_insn_opcode == OpRegReg && d_insn[31:25] == 7'd1 && d_insn[14:12] == 3'b111;

  wire d_insn_ecall = d_insn_opcode == OpEnviron && d_insn[31:7] == 25'd0;
  wire d_insn_fence = d_insn_opcode == OpMiscMem;

  logic [5:0] d_insn_name;
  localparam bit [5:0] InsnLui = 6'd1;
  localparam bit [5:0] InsnAuipc = 6'd2;
  localparam bit [5:0] InsnJal = 6'd3;
  localparam bit [5:0] InsnJalr = 6'd4;
  localparam bit [5:0] InsnBeq = 6'd5;
  localparam bit [5:0] InsnBne = 6'd6;
  localparam bit [5:0] InsnBlt = 6'd7;
  localparam bit [5:0] InsnBge = 6'd8;
  localparam bit [5:0] InsnBltu = 6'd9;
  localparam bit [5:0] InsnBgeu = 6'd10;
  localparam bit [5:0] InsnLb = 6'd11;
  localparam bit [5:0] InsnLh = 6'd12;
  localparam bit [5:0] InsnLw = 6'd13;
  localparam bit [5:0] InsnLbu = 6'd14;
  localparam bit [5:0] InsnLhu = 6'd15;
  localparam bit [5:0] InsnSb = 6'd16;
  localparam bit [5:0] InsnSh = 6'd17;
  localparam bit [5:0] InsnSw = 6'd18;
  localparam bit [5:0] InsnAddi = 6'd19;
  localparam bit [5:0] InsnSlti = 6'd20;
  localparam bit [5:0] InsnSltiu = 6'd21;
  localparam bit [5:0] InsnXori = 6'd22;
  localparam bit [5:0] InsnOri = 6'd23;
  localparam bit [5:0] InsnAndi = 6'd24;
  localparam bit [5:0] InsnSlli = 6'd25;
  localparam bit [5:0] InsnSrli = 6'd26;
  localparam bit [5:0] InsnSrai = 6'd27;
  localparam bit [5:0] InsnAdd = 6'd28;
  localparam bit [5:0] InsnSub = 6'd29;
  localparam bit [5:0] InsnSll = 6'd30;
  localparam bit [5:0] InsnSlt = 6'd31;
  localparam bit [5:0] InsnSltu = 6'd32;
  localparam bit [5:0] InsnXor = 6'd33;
  localparam bit [5:0] InsnSrl = 6'd34;
  localparam bit [5:0] InsnSra = 6'd35;
  localparam bit [5:0] InsnOr = 6'd36;
  localparam bit [5:0] InsnAnd = 6'd37;
  localparam bit [5:0] InsnMul = 6'd38;
  localparam bit [5:0] InsnMulh = 6'd39;
  localparam bit [5:0] InsnMulhsu = 6'd40;
  localparam bit [5:0] InsnMulhu = 6'd41;
  localparam bit [5:0] InsnDiv = 6'd42;
  localparam bit [5:0] InsnDivu = 6'd43;
  localparam bit [5:0] InsnRem = 6'd44;
  localparam bit [5:0] InsnRemu = 6'd45;
  localparam bit [5:0] InsnEcall = 6'd46;
  localparam bit [5:0] InsnFence = 6'd47;

  assign d_insn_name = d_insn_lui ? InsnLui : 
    (d_insn_auipc ? InsnAuipc : 
    (d_insn_jal ? InsnJal : 
    (d_insn_jalr ? InsnJalr :
    (d_insn_beq ? InsnBeq :
    (d_insn_bne ? InsnBne :
    (d_insn_blt ? InsnBlt :
    (d_insn_bge ? InsnBge :
    (d_insn_bltu ? InsnBltu :
    (d_insn_bgeu ? InsnBgeu :
    (d_insn_lb ? InsnLb :
    (d_insn_lh ? InsnLh :
    (d_insn_lw ? InsnLw :
    (d_insn_lbu ? InsnLbu :
    (d_insn_lhu ? InsnLhu :
    (d_insn_sb ? InsnSb :
    (d_insn_sh ? InsnSh :
    (d_insn_sw ? InsnSw :
    (d_insn_addi ? InsnAddi :
    (d_insn_slti ? InsnSlti :
    (d_insn_sltiu ? InsnSltiu :
    (d_insn_xori ? InsnXori :
    (d_insn_ori ? InsnOri :
    (d_insn_andi ? InsnAndi :
    (d_insn_slli ? InsnSlli :
    (d_insn_srli ? InsnSrli :
    (d_insn_srai ? InsnSrai :
    (d_insn_add ? InsnAdd :
    (d_insn_sub ? InsnSub :
    (d_insn_sll ? InsnSll :
    (d_insn_slt ? InsnSlt :
    (d_insn_sltu ? InsnSltu :
    (d_insn_xor ? InsnXor :
    (d_insn_srl ? InsnSrl :
    (d_insn_sra ? InsnSra :
    (d_insn_or ? InsnOr :
    (d_insn_and ? InsnAnd :
    (d_insn_mul ? InsnMul :
    (d_insn_mulh ? InsnMulh :
    (d_insn_mulhsu ? InsnMulhsu :
    (d_insn_mulhu ? InsnMulhu :
    (d_insn_div ? InsnDiv :
    (d_insn_divu ? InsnDivu :
    (d_insn_rem ? InsnRem :
    (d_insn_remu ? InsnRemu :
    (d_insn_ecall ? InsnEcall :
    (d_insn_fence ? InsnFence : 6'd0
    ))))))))))))))))))))))))))))))))))))))))))))));

  logic d_is_save_insn;
  always_comb begin
    if (d_insn_name == InsnSb) begin
      d_is_save_insn = 1;
    end else if (d_insn_name == InsnSh) begin
      d_is_save_insn = 1;
    end else if (d_insn_name == InsnSw) begin
      d_is_save_insn = 1;
    end else begin
      d_is_save_insn = 0;
    end
  end

  // STALLING BC OF FENCE
  // Logic:
  // - Check if decode stage currently has a fence insn
  // - Check if there is any save insn in execute or memory
  logic d_fence_stall;
  always_comb begin
    if ((d_insn_name == InsnFence) && (x_is_save_insn || m_is_save_insn)) begin
      d_fence_stall = 1;
    end else begin
      d_fence_stall = 0;
    end
  end

  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,
          imm_s_sext: 0,
          imm_j_sext: 0,

          insn_name: 0
      };
    end else if (x_load_stall) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_LOAD2USE,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,
          imm_s_sext: 0,
          imm_j_sext: 0,

          insn_name: 0
      };
    end else if (x_divide_to_use_stall) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_DIV2USE,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,
          imm_s_sext: 0,
          imm_j_sext: 0,

          insn_name: 0
      };
    end else if (x_branching) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_TAKEN_BRANCH,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,
          imm_s_sext: 0,
          imm_j_sext: 0,

          insn_name: 0
      };
    end else begin
      begin
        execute_state <= '{
            pc: decode_state.pc,
            insn: d_insn,
            cycle_status: decode_state.cycle_status,

            rs1: d_insn_rs1,
            rs2: d_insn_rs2,
            rd: d_insn_rd,

            imm_u: d_imm_u,
            imm_i_4_0: d_imm_i_4_0,
            imm_i_sext: d_imm_i_sext,
            imm_b_sext: d_imm_b_sext,
            imm_s_sext: d_imm_s_sext,
            imm_j_sext: d_imm_j_sext,

            insn_name: d_insn_name
        };
      end
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

  // TODO: the testbench requires that your register file instance is named `rf`

  // // //
  // EXECUTE: Modules Used
  // // //

  logic [4:0] x_rs1, x_rd;
  logic [`REG_SIZE] x_rd_data_inter;
  logic [`REG_SIZE] x_rd_data, x_rs1_data, x_rs2_data;
  logic [4:0] x_rs2_data_4_0;

  logic x_we;
  logic x_halt;

  // For branching
  logic [`REG_SIZE] x_branch_pc;
  logic x_branching;
  logic [`REG_SIZE] int_one;

  // MX and WX bypassing
  // - First we check for a MX bypass, i.e. if x-rs1 = m-rd
  // - Otherwise, we check for a WX bypass, i.e. if x-rs1 = w-rd
  // - Otherwise, we just use the value we got from the register file
  // - We also don't want to do the 
  logic [`REG_SIZE] x_bp_rs1_data, x_bp_rs2_data;
  assign x_bp_rs1_data = ((execute_state.rs1 == memory_state.rd) && (execute_state.rs1 != 0)) ? memory_state.rd_data : (
    ((execute_state.rs1 == writeback_state.rd) && (execute_state.rs1 != 0)) ? writeback_state.rd_data : x_rs1_data
  );
  assign x_bp_rs2_data = ((execute_state.rs2 == memory_state.rd) && (execute_state.rs2 != 0)) ? memory_state.rd_data : (
    ((execute_state.rs2 == writeback_state.rd) && (execute_state.rs2 != 0)) ? writeback_state.rd_data : x_rs2_data
  );
  assign x_rs2_data_4_0 = x_bp_rs2_data[4:0];

  // CLA stuff
  logic [`REG_SIZE] x_cla_a, x_cla_b;

  cla x_cla (
      .a  (x_cla_a),
      .b  (x_cla_b),
      .cin(1'b0),
      .sum(x_rd_data_inter)
  );

  logic [`REG_SIZE] x_cla_inc_in, x_cla_inc_out;
  logic [`REG_SIZE] x_cla_one = 32'b1;

  cla x_cla_incr (
      .a  (x_cla_inc_in),
      .b  (x_cla_one),
      .cin(1'b0),
      .sum(x_cla_inc_out)
  );

  // DIV stuff

  logic [`REG_SIZE] x_div_a, x_div_b;
  logic [`REG_SIZE] m_div_iter2_remainder, m_div_iter2_quotient;
  logic [`REG_SIZE] m_div_iter2_quotient_flipped, m_div_iter2_remainder_flipped;
  logic [`REG_SIZE] x_divide_by_zero, x_div_flip_sign;

  divider_unsigned_pipelined unsigned_div (
      .clk(clk),
      .rst(rst),
      .i_dividend(x_div_a),
      .i_divisor(x_div_b),
      // remainder and quotient for the a and b in the execute stage will be ready in the memory stage
      .o_remainder(m_div_iter2_remainder),
      .o_quotient(m_div_iter2_quotient)
  );

  // LOADS AND STALLING
  logic x_is_load_insn;
  always_comb begin
    if (execute_state.insn_name == InsnLb) begin
      x_is_load_insn = 1;
    end else if (execute_state.insn_name == InsnLbu) begin
      x_is_load_insn = 1;
    end else if (execute_state.insn_name == InsnLh) begin
      x_is_load_insn = 1;
    end else if (execute_state.insn_name == InsnLhu) begin
      x_is_load_insn = 1;
    end else if (execute_state.insn_name == InsnLw) begin
      x_is_load_insn = 1;
    end else begin
      x_is_load_insn = 0;
    end
  end

  logic x_is_save_insn;
  always_comb begin
    if (execute_state.insn_name == InsnSb) begin
      x_is_save_insn = 1;
    end else if (execute_state.insn_name == InsnSh) begin
      x_is_save_insn = 1;
    end else if (execute_state.insn_name == InsnSw) begin
      x_is_save_insn = 1;
    end else begin
      x_is_save_insn = 0;
    end
  end

  logic x_load_stall;
  always_comb begin
    // We DON'T want to stall if the next insn is a save one
    // ALSO: make sure we check if rs1 or rs2 are zero, in which case we shouldn't stall (since x0=0 always)
    // - we automatically set rs1_fixed and rs2_fixed to zero if they are unused for an insn (see above)
    if (x_is_load_insn && (execute_state.rd == d_insn_rs1_fixed) && (d_insn_rs1_fixed != 0)) begin
      x_load_stall = 1;
      // If the next insn is a save one and we're using rs2, we DON'T need to stall
      // We also need to make sure that this doesn't apply to insns that don't use rs2
    end else if (x_is_load_insn && (execute_state.rd == d_insn_rs2_fixed) && (d_is_save_insn == 0) && (d_insn_rs2_fixed != 0)) begin
      x_load_stall = 1;
    end else begin
      x_load_stall = 0;
    end
  end

  // DIVs
  logic x_is_div_insn;
  always_comb begin
    if (execute_state.insn_name == InsnDiv) begin
      x_is_div_insn = 1;
    end else if (execute_state.insn_name == InsnDivu) begin
      x_is_div_insn = 1;
    end else if (execute_state.insn_name == InsnRem) begin
      x_is_div_insn = 1;
    end else if (execute_state.insn_name == InsnRemu) begin
      x_is_div_insn = 1;
    end else begin
      x_is_div_insn = 0;
    end
  end

  logic x_divide_to_use_stall;
  always_comb begin
    if (x_is_div_insn && (execute_state.rd == d_insn_rs1_fixed) && (d_insn_rs1_fixed != 0)) begin
      x_divide_to_use_stall = 1;
    end else if (x_is_div_insn && (execute_state.rd == d_insn_rs2_fixed) && (d_insn_rs2_fixed != 0)) begin
      x_divide_to_use_stall = 1;
    end else begin
      x_divide_to_use_stall = 0;
    end
  end

  // CALCULATING MEMORY ADDRESS

  logic [`REG_SIZE] x_unaligned_addr_to_dmem;
  logic [`REG_SIZE] x_addr_to_dmem;

  // MUL STUFF
  logic [63:0] x_mul_result;

  // JUMP STUFF
  logic [`REG_SIZE] x_jalr_int_value;

  // // //
  // EXECUTE: Logic
  // // //

  always_comb begin
    x_rd = 0;
    x_rd_data = 0;
    x_we = 0;
    x_cla_inc_in = 0;
    x_cla_a = 0;
    x_cla_b = 0;
    x_div_a = 0;
    x_div_b = 0;

    x_mul_result = 0;

    int_one = 0;
    x_divide_by_zero = 0;
    x_div_flip_sign = 0;

    x_jalr_int_value = 0;

    x_halt = 0;

    // Branching
    x_branching = 0;
    x_branch_pc = execute_state.pc;

    // Loads
    x_unaligned_addr_to_dmem = 0;
    x_addr_to_dmem = 0;

    m_div_iter2_quotient_flipped = ~m_div_iter2_quotient + 1;
    m_div_iter2_remainder_flipped = ~m_div_iter2_remainder + 1;

    // Perform arithmetic based on instruction
    case (execute_state.insn_name)

      // Arithmetic Insns
      // Immediates
      InsnLui: begin
        x_rd = execute_state.rd;
        x_rd_data = {execute_state.imm_u, 12'b0};
        x_we = 1;
      end

      InsnAuipc: begin
        x_rd = execute_state.rd;
        x_rd_data = execute_state.pc + {execute_state.imm_u, 12'b0};
        x_we = 1;
      end

      InsnAddi: begin
        x_cla_a = x_bp_rs1_data;
        x_cla_b = execute_state.imm_i_sext;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnSlti: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) < $signed(execute_state.imm_i_sext) ? 1 : 0;
        x_we = 1;
      end

      InsnSltiu: begin
        x_rd = execute_state.rd;
        x_rd_data = $unsigned(x_bp_rs1_data) < $unsigned(execute_state.imm_i_sext) ? 1 : 0;
        x_we = 1;
      end

      InsnXori: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data ^ execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnOri: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data | execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnAndi: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data & execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnSlli: begin
        // Note: To fix this I implemented a new thing in decode/execute stage: d_imm_i_4_0. in decode stage it takes [4:0] from d_imm_i

        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data << execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSrli: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data >> execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSrai: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) >>> execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSltu: begin
        x_rd = execute_state.rd;
        x_rd_data = $unsigned(x_bp_rs1_data) < $unsigned(x_bp_rs2_data) ? 1 : 0;
        x_we = 1;
      end

      // RegReg
      InsnAdd: begin
        x_cla_a = x_bp_rs1_data;
        x_cla_b = x_bp_rs2_data;
        x_cla_inc_in = 0;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnSub: begin
        x_cla_inc_in = ~x_bp_rs2_data;  // invert all the bits
        x_cla_b = x_cla_inc_out;  // add 1

        x_cla_a = x_bp_rs1_data;
        x_cla_b = x_cla_inc_out;
        x_cla_inc_in = ~x_bp_rs2_data;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnAnd: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data & x_bp_rs2_data;
        x_we = 1;
      end

      InsnOr: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data | x_bp_rs2_data;
        x_we = 1;
      end

      InsnXor: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data ^ x_bp_rs2_data;
        x_we = 1;
      end

      InsnSlt: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) < $signed(x_bp_rs2_data) ? 1 : 0;
        x_we = 1;
      end

      InsnSll: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data << x_rs2_data_4_0;
        x_we = 1;
      end

      InsnSrl: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data >> x_rs2_data_4_0;
        x_we = 1;
      end

      InsnSra: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) >>> x_rs2_data_4_0;
        x_we = 1;
      end

      InsnMul: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data * x_bp_rs2_data;
        x_we = 1;
      end

      InsnMulh: begin
        x_rd = execute_state.rd;
        x_mul_result = $signed(x_bp_rs1_data) * $signed(x_bp_rs2_data);
        x_rd_data = x_mul_result[63:32];
        x_we = 1;
      end

      InsnMulhsu: begin
        x_rd = execute_state.rd;
        x_mul_result = $signed(x_bp_rs1_data) * $signed({1'b0, x_bp_rs2_data});
        x_rd_data = x_mul_result[63:32];
        x_we = 1;
      end

      InsnMulhu: begin
        x_rd = execute_state.rd;
        x_mul_result = $unsigned(x_bp_rs1_data) * $unsigned(x_bp_rs2_data);
        x_rd_data = x_mul_result[63:32];
        x_we = 1;
      end

      // Branch Insns

      /* 
        On a taken branch, your datapath will flush the instructions in Fetch and Decode 
        (replacing them with NOPs/bubbles) and then fetch the correct-path instruction 
        in the following cycle (when the branch moves to the Memory stage). The pipelining 
        lecture slides discuss the cycle timing in detail.
      */

      InsnBeq: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if (x_bp_rs1_data == x_bp_rs2_data) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBne: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if (x_bp_rs1_data != x_bp_rs2_data) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBlt: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if ($signed(x_bp_rs1_data) < $signed(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBge: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($signed(x_bp_rs1_data) >= $signed(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBltu: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($unsigned(x_bp_rs1_data) < $unsigned(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBgeu: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($unsigned(x_bp_rs1_data) >= $unsigned(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      /* JUMP INSNS */

      InsnJal: begin
        x_rd = execute_state.rd;
        x_rd_data = execute_state.pc + 32'd4;
        x_we = 1;

        x_branch_pc = execute_state.pc + execute_state.imm_j_sext;
        x_branching = 1;
      end

      InsnJalr: begin
        x_rd = execute_state.rd;
        x_rd_data = execute_state.pc + 32'd4;
        x_we = 1;

        x_jalr_int_value = (x_bp_rs1_data + execute_state.imm_i_sext) & ~(32'd1);
        x_branch_pc = {x_jalr_int_value[31:2], 2'b0};
        x_branching = 1;
      end

      /* LOAD INSNS */
      InsnLb: begin
        x_rd = execute_state.rd;
        x_we = 1;

        // Set unaligned address
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_i_sext);
      end

      InsnLh: begin
        x_rd = execute_state.rd;
        x_we = 1;

        // Set unaligned address
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_i_sext);
      end

      InsnLw: begin
        x_rd = execute_state.rd;
        x_we = 1;

        // Set unaligned address
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_i_sext);
      end

      InsnLbu: begin
        x_rd = execute_state.rd;
        x_we = 1;

        // Set unaligned address
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_i_sext);
      end

      InsnLhu: begin
        x_rd = execute_state.rd;
        x_we = 1;

        // Set unaligned address
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_i_sext);
      end

      /* SAVE INSNS */
      InsnSb: begin
        x_we = 0;
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_s_sext);
      end

      InsnSh: begin
        x_we = 0;
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_s_sext);
      end

      InsnSw: begin
        x_we = 0;
        x_addr_to_dmem = $signed(x_bp_rs1_data) + $signed(execute_state.imm_s_sext);
      end

      /* MISC INSNS */
      InsnFence: begin
        x_we = 0;
      end

      InsnEcall: begin
        x_we   = 0;
        x_halt = 1;
      end

      InsnDiv: begin
        if (x_bp_rs2_data == 0) begin
          // set flag to return -1
          x_divide_by_zero = 1;
          int_one = 1;
          x_rd_data = $signed(~int_one + 1);
        end else if (x_bp_rs1_data[31] == 1 && x_bp_rs2_data[31] == 0) begin
          x_div_a = ~x_bp_rs1_data + 1;
          x_div_b = x_bp_rs2_data;
          x_div_flip_sign = 1;
        end else if (x_bp_rs1_data[31] == 0 && x_bp_rs2_data[31] == 1) begin
          x_div_a = x_bp_rs1_data;
          x_div_b = ~x_bp_rs2_data + 1;
          x_div_flip_sign = 1;
        end else if (x_bp_rs1_data[31] == 1 && x_bp_rs2_data[31] == 1) begin
          x_div_a = ~x_bp_rs1_data + 1;
          x_div_b = ~x_bp_rs2_data + 1;
          x_div_flip_sign = 0;
        end else begin
          x_div_a = x_bp_rs1_data;
          x_div_b = x_bp_rs2_data;
          x_divide_by_zero = 0;
        end

        x_rd = execute_state.rd;
        x_we = 1;
      end

      InsnDivu: begin
        if (x_bp_rs2_data == 0) begin
          // set flag to return -1
          x_divide_by_zero = 1;
          int_one = 1;
          x_rd_data = $unsigned(~int_one + 1);
        end else begin
          x_div_a = x_bp_rs1_data;
          x_div_b = x_bp_rs2_data;
          x_divide_by_zero = 0;
        end

        x_rd = execute_state.rd;
        x_we = 1;
      end

      InsnRem: begin
        if (x_bp_rs2_data == 0) begin
          // set flag to return -1
          x_divide_by_zero = 1;
          x_rd_data = x_bp_rs1_data;
        end else if (x_bp_rs1_data[31] == 1 && x_bp_rs2_data[31] == 0) begin
          x_div_a = ~x_bp_rs1_data + 1;
          x_div_b = x_bp_rs2_data;
          x_div_flip_sign = 1;
        end else if (x_bp_rs1_data[31] == 0 && x_bp_rs2_data[31] == 1) begin
          x_div_a = x_bp_rs1_data;
          x_div_b = ~x_bp_rs2_data + 1;
          x_div_flip_sign = 0;
        end else if (x_bp_rs1_data[31] == 1 && x_bp_rs2_data[31] == 1) begin
          x_div_a = ~x_bp_rs1_data + 1;
          x_div_b = ~x_bp_rs2_data + 1;
          x_div_flip_sign = 1;
        end else begin
          x_div_a = x_bp_rs1_data;
          x_div_b = x_bp_rs2_data;
          x_divide_by_zero = 0;
        end

        x_rd = execute_state.rd;
        x_we = 1;
      end

      InsnRemu: begin
        if (x_bp_rs2_data == 0) begin
          // set flag to return -1
          x_divide_by_zero = 1;
          x_rd_data = x_bp_rs1_data;
        end else begin
          x_div_a = x_bp_rs1_data;
          x_div_b = x_bp_rs2_data;
          x_divide_by_zero = 0;
        end

        x_rd = execute_state.rd;
        x_we = 1;
      end

      default: begin
        x_we = 0;
      end
    endcase
  end

  /****************/
  /* MEMORY STAGE */
  /****************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rd: 0,
          rs2: 0,
          rd_data: 0,
          rs2_data: 0,

          insn_name: 0,
          is_load_insn: 0,
          divide_by_zero: 0,
          divide_flip_sign: 0,

          addr_to_dmem: 0,

          we: 0,
          halt: 0
      };
    end else begin
      begin
        memory_state <= '{
            pc: execute_state.pc,  // Even if we branch, we should propagate the old pc here
            insn: execute_state.insn,
            cycle_status: execute_state.cycle_status,

            rd: x_rd,
            rs2: execute_state.rs2,
            rd_data: x_rd_data,
            rs2_data: x_bp_rs2_data,

            insn_name: execute_state.insn_name,
            is_load_insn: x_is_load_insn,
            divide_by_zero: x_divide_by_zero,
            divide_flip_sign: x_div_flip_sign,

            addr_to_dmem: x_addr_to_dmem,

            we: x_we,
            halt: x_halt
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (execute_state.insn),
      .disasm(m_disasm)
  );


  logic [`REG_SIZE] m_rd_data;
  logic [`REG_SIZE] m_bp_rs2_data;
  logic [`REG_SIZE] m_addr_to_dmem;

  logic m_is_save_insn;
  always_comb begin
    if (memory_state.insn_name == InsnSb) begin
      m_is_save_insn = 1;
    end else if (memory_state.insn_name == InsnSh) begin
      m_is_save_insn = 1;
    end else if (memory_state.insn_name == InsnSw) begin
      m_is_save_insn = 1;
    end else begin
      m_is_save_insn = 0;
    end
  end

  // WM bypassing
  // Checks:
  // - Writeback state has a load insn
  // - Memory state has a save insn
  // - rs2 in memory state is rd in writeback state
  assign m_bp_rs2_data = ((memory_state.rs2 == writeback_state.rd) && writeback_state.is_load_insn && m_is_save_insn) ? writeback_state.rd_data : memory_state.rs2_data;

  always_comb begin
    m_addr_to_dmem = 0;
    dmem.WSTRB = 0;
    dmem.WVALID = 0;
    dmem.AWVALID = 0;

    case (memory_state.insn_name)

      /*
        x_div_a=div1_rs1_data, x_div_b=div1_rs2_data, w_div_iter2=quotient=not ready
        x_div_a=div2_rs1_data, x_div_b=div2_rs2_data, w_div_iter2=div1_x_quotient
                                                      w_div_iter2=div2_x_quotient
      */

      /* LOAD INSNS */
      InsnLb: begin
        m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

        // Choose which byte of the loaded word to take
        // We also need to sign-extend our result manually
        case (memory_state.addr_to_dmem[1:0])
          2'b00: begin
            m_rd_data = {{24{dmem.RDATA[7]}}, dmem.RDATA[7:0]};
          end
          2'b01: begin
            m_rd_data = {{24{dmem.RDATA[15]}}, dmem.RDATA[15:8]};
          end
          2'b10: begin
            m_rd_data = {{24{dmem.RDATA[23]}}, dmem.RDATA[23:16]};
          end
          2'b11: begin
            m_rd_data = {{24{dmem.RDATA[31]}}, dmem.RDATA[31:24]};
          end
          default: begin
          end
        endcase
      end

      InsnLbu: begin
        m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

        // Choose which byte of the loaded word to take
        // We also need to ZERO-extend our result manually
        case (memory_state.addr_to_dmem[1:0])
          2'b00: begin
            m_rd_data = {24'b0, dmem.RDATA[7:0]};
          end
          2'b01: begin
            m_rd_data = {24'b0, dmem.RDATA[15:8]};
          end
          2'b10: begin
            m_rd_data = {24'b0, dmem.RDATA[23:16]};
          end
          2'b11: begin
            m_rd_data = {24'b0, dmem.RDATA[31:24]};
          end
          default: begin
          end
        endcase
      end

      InsnLh: begin

        // Only allow aligned addresses (last bit must be 0)
        if (memory_state.addr_to_dmem[0] == 0) begin
          m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

          case (memory_state.addr_to_dmem[1])
            1'b0: begin
              m_rd_data = {{16{dmem.RDATA[15]}}, dmem.RDATA[15:0]};
            end
            1'b1: begin
              m_rd_data = {{16{dmem.RDATA[31]}}, dmem.RDATA[31:16]};
            end
            default: begin
            end
          endcase
        end
      end

      InsnLhu: begin

        // Only allow aligned addresses (last bit must be 0)
        if (memory_state.addr_to_dmem[0] == 0) begin
          m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

          case (memory_state.addr_to_dmem[1])
            1'b0: begin
              m_rd_data = {16'b0, dmem.RDATA[15:0]};
            end
            1'b1: begin
              m_rd_data = {16'b0, dmem.RDATA[31:16]};
            end
            default: begin
            end
          endcase
        end
      end

      InsnLw: begin

        // Only allow aligned addresses (last two bits must be 0)
        if (memory_state.addr_to_dmem[1:0] == 2'b0) begin
          m_rd_data = dmem.RDATA;
          m_addr_to_dmem = memory_state.addr_to_dmem;
        end
      end

      /* SAVE INSNS */
      InsnSb: begin
        dmem.WVALID = 1;
        dmem.AWVALID = 1;
        m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

        case (memory_state.addr_to_dmem[1:0])
          2'b00: begin
            dmem.WSTRB = 4'b0001;
            dmem.WDATA = {24'b0, m_bp_rs2_data[7:0]};
          end
          2'b01: begin
            dmem.WSTRB = 4'b0010;
            dmem.WDATA = {16'b0, m_bp_rs2_data[7:0], 8'b0};
          end
          2'b10: begin
            dmem.WSTRB = 4'b0100;
            dmem.WDATA = {8'b0, m_bp_rs2_data[7:0], 16'b0};
          end
          2'b11: begin
            dmem.WSTRB = 4'b1000;
            dmem.WDATA = {m_bp_rs2_data[7:0], 24'b0};
          end
          default: begin
          end
        endcase
      end

      InsnSh: begin
        dmem.WVALID  = 1;
        dmem.AWVALID = 1;
        if (memory_state.addr_to_dmem[0] == 0) begin
          m_addr_to_dmem = {memory_state.addr_to_dmem[31:2], 2'b0};

          // Choose which byte to store in this word
          case (memory_state.addr_to_dmem[1])
            1'b0: begin
              dmem.WSTRB = 4'b0011;
              dmem.WDATA = {16'b0, m_bp_rs2_data[15:0]};
            end
            1'b1: begin
              dmem.WSTRB = 4'b1100;
              dmem.WDATA = {m_bp_rs2_data[15:0], 16'b0};
            end
            default: begin
            end
          endcase
        end
      end

      InsnSw: begin
        dmem.WVALID  = 1;
        dmem.AWVALID = 1;
        if (memory_state.addr_to_dmem[1:0] == 2'b0) begin
          m_addr_to_dmem = memory_state.addr_to_dmem;
          dmem.WSTRB = 4'b1111;
          dmem.WDATA = m_bp_rs2_data;
        end
      end

      InsnDiv: begin
        if (memory_state.divide_by_zero == 1) begin
          m_rd_data = memory_state.rd_data;
        end else if (memory_state.divide_flip_sign == 1) begin
          m_rd_data = m_div_iter2_quotient_flipped;
        end else begin
          m_rd_data = m_div_iter2_quotient;
        end
      end

      InsnDivu: begin
        if (memory_state.divide_by_zero == 1) begin
          m_rd_data = memory_state.rd_data;
        end else begin
          m_rd_data = m_div_iter2_quotient;
        end
      end

      InsnRem: begin
        if (memory_state.divide_by_zero == 1) begin
          m_rd_data = memory_state.rd_data;
        end else if (memory_state.divide_flip_sign == 1) begin
          m_rd_data = m_div_iter2_remainder_flipped;
        end else begin
          m_rd_data = m_div_iter2_remainder;
        end
      end

      InsnRemu: begin
        if (memory_state.divide_by_zero == 1) begin
          m_rd_data = memory_state.rd_data;
        end else begin
          m_rd_data = m_div_iter2_remainder;
        end
      end

      default: begin
        m_rd_data = memory_state.rd_data;
      end
    endcase
  end

  // Update addr_to_dmem
  always_comb begin
    dmem.ARVALID = 1;
    dmem.ARADDR  = m_addr_to_dmem;
  end


  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rd: 0,
          rd_data: 0,

          is_load_insn: 0,

          we: memory_state.we,
          halt: memory_state.halt
      };
    end else begin
      begin
        writeback_state <= '{
            pc: memory_state.pc,
            insn: memory_state.insn,
            cycle_status: memory_state.cycle_status,

            rd: memory_state.rd,
            rd_data: m_rd_data,

            is_load_insn: memory_state.is_load_insn,

            we: memory_state.we,
            halt: memory_state.halt
        };
      end
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (memory_state.insn),
      .disasm(w_disasm)
  );

  // Traces
  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

  logic w_we;
  logic [`REG_SIZE] w_rd_data;

  // Writing back to register files
  always_comb begin
    if (writeback_state.we == 1) begin
      w_rd_data = writeback_state.rd_data;
      w_we = writeback_state.we;
    end else begin
      w_rd_data = 0;
      w_we = 0;
    end

    // More instructions here...

    // Set halt appropriately
    halt = writeback_state.halt;
  end

endmodule

// module MemorySingleCycle #(
//     parameter int NUM_WORDS = 512
// ) (
//     // rst for both imem and dmem
//     input wire rst,

//     // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
//     input wire clk,

//     // must always be aligned to a 4B boundary
//     input wire [`REG_SIZE] pc_to_imem,

//     // the value at memory location pc_to_imem
//     output logic [`REG_SIZE] insn_from_imem,

//     // must always be aligned to a 4B boundary
//     input wire [`REG_SIZE] addr_to_dmem,

//     // the value at memory location addr_to_dmem
//     output logic [`REG_SIZE] load_data_from_dmem,

//     // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
//     input wire [`REG_SIZE] store_data_to_dmem,

//     // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
//     // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
//     input wire [3:0] store_we_to_dmem
// );

//   // memory is arranged as an array of 4B words
//   logic [`REG_SIZE] mem[NUM_WORDS];

//   initial begin
//     $readmemh("mem_initial_contents.hex", mem, 0);
//   end

//   always_comb begin
//     // memory addresses should always be 4B-aligned
//     assert (pc_to_imem[1:0] == 2'b00);
//     assert (addr_to_dmem[1:0] == 2'b00);
//   end

//   localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
//   localparam int AddrLsb = 2;

//   always @(negedge clk) begin
//     if (rst) begin
//     end else begin
//       insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
//     end
//   end

//   always @(negedge clk) begin
//     if (rst) begin
//     end else begin
//       if (store_we_to_dmem[0]) begin
//         mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
//       end
//       if (store_we_to_dmem[1]) begin
//         mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
//       end
//       if (store_we_to_dmem[2]) begin
//         mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
//       end
//       if (store_we_to_dmem[3]) begin
//         mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
//       end
//       // dmem is "read-first": read returns value before the write
//       load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
//     end
//   end
// endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
  // wire [`INSN_SIZE] insn_from_imem;
  // wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  // wire [3:0] mem_data_we;
  // MemorySingleCycle #(
  //     .NUM_WORDS(8192)
  // ) the_mem (
  //     .rst                (rst),
  //     .clk                (clk),
  //     // imem is read-only
  //     .pc_to_imem         (pc_to_imem),
  //     .insn_from_imem     (insn_from_imem),
  //     // dmem is read-write
  //     .addr_to_dmem       (mem_data_addr),
  //     .load_data_from_dmem(mem_data_loaded_value),
  //     .store_data_to_dmem (mem_data_to_write),
  //     .store_we_to_dmem   (mem_data_we)
  // );

  // HW6 memory interface
  axi_clkrst_if axi_cr (
      .ACLK(clk),
      .ARESETn(~rst)
  );
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(
      .NUM_WORDS(8192)
  ) mem (
      .axi (axi_cr),
      .insn(axi_insn.subord),
      .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk (clk),
      .rst (rst),
      .imem(axi_insn.manager),
      // .pc_to_imem(pc_to_imem),
      // .insn_from_imem(insn_from_imem),
      .dmem(axi_data.manager),

      // .addr_to_dmem(mem_data_addr),
      // .load_data_from_dmem(mem_data_loaded_value),
      // .store_data_to_dmem(mem_data_to_write),
      // .store_we_to_dmem(mem_data_we),


      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
