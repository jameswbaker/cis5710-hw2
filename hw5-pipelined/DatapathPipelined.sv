`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

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

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
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
  logic [`REG_SIZE] imm_i_sext;

  logic insn_lui;
  logic insn_auipc;
  logic insn_jal;
  logic insn_jalr;
  logic insn_beq;
  logic insn_bne;
  logic insn_blt;
  logic insn_bge;
  logic insn_bltu;
  logic insn_bgeu;
  logic insn_lb;
  logic insn_lh;
  logic insn_lw;
  logic insn_lbu;
  logic insn_lhu;
  logic insn_sb;
  logic insn_sh;
  logic insn_sw;
  logic insn_addi;
  logic insn_slti;
  logic insn_sltiu;
  logic insn_xori;
  logic insn_ori;
  logic insn_andi;
  logic insn_slli;
  logic insn_srli;
  logic insn_srai;
  logic insn_add;
  logic insn_sub;
  logic insn_sll;
  logic insn_slt;
  logic insn_sltu;
  logic insn_xor;
  logic insn_srl;
  logic insn_sra;
  logic insn_or;
  logic insn_and;
  logic insn_mul;
  logic insn_mulh;
  logic insn_mulhsu;
  logic insn_mulhu;
  logic insn_div;
  logic insn_divu;
  logic insn_rem;
  logic insn_remu;
  logic insn_ecall;
  logic insn_fence;
} stage_execute_t;

/** memory state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;

  logic we;
} stage_memory_t;

/** writeback state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;

  logic we;
} stage_writeback_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

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

  // opcodes - see section 19 of RiscV spec
  // localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  // localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  // localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  // localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  // localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
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
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current   <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET};
    end else begin
      begin
        decode_state <= '{pc: f_pc_current, insn: f_insn, cycle_status: f_cycle_status};
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
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
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = decode_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] d_imm_i;
  assign d_imm_i = decode_state.insn[31:20];
  wire [ 4:0] d_imm_shamt = decode_state.insn[24:20];

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
    decode_state.insn[31:12], 1'b0
  };

  // U - setup for U type instructions
  wire [19:0] d_imm_u;
  assign d_imm_u = decode_state.insn[31:12];

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

  wire d_insn_beq = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b000;
  wire d_insn_bne = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b001;
  wire d_insn_blt = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b100;
  wire d_insn_bge = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b101;
  wire d_insn_bltu = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b110;
  wire d_insn_bgeu = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b111;

  wire d_insn_lb = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b000;
  wire d_insn_lh = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b001;
  wire d_insn_lw = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b010;
  wire d_insn_lbu = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b100;
  wire d_insn_lhu = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b101;

  wire d_insn_sb = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b000;
  wire d_insn_sh = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b001;
  wire d_insn_sw = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b010;

  wire d_insn_addi = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b000;
  wire d_insn_slti = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b010;
  wire d_insn_sltiu = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b011;
  wire d_insn_xori = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b100;
  wire d_insn_ori = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b110;
  wire d_insn_andi = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b111;

  wire d_insn_slli = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srli = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srai = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;

  wire d_insn_add = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sub  = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'b0100000;
  wire d_insn_sll = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_slt = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b010 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sltu = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b011 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_xor = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b100 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srl = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sra  = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;
  wire d_insn_or = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b110 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_and = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b111 && decode_state.insn[31:25] == 7'd0;

  wire d_insn_mul    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b000;
  wire d_insn_mulh   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b001;
  wire d_insn_mulhsu = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b010;
  wire d_insn_mulhu  = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b011;
  wire d_insn_div    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b100;
  wire d_insn_divu   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b101;
  wire d_insn_rem    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b110;
  wire d_insn_remu   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b111;

  wire d_insn_ecall = d_insn_opcode == OpEnviron && decode_state.insn[31:7] == 25'd0;
  wire d_insn_fence = d_insn_opcode == OpMiscMem;

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
          imm_i_sext: 0,

          insn_lui: 0,
          insn_auipc: 0,
          insn_jal: 0,
          insn_jalr: 0,
          insn_beq: 0,
          insn_bne: 0,
          insn_blt: 0,
          insn_bge: 0,
          insn_bltu: 0,
          insn_bgeu: 0,
          insn_lb: 0,
          insn_lh: 0,
          insn_lw: 0,
          insn_lbu: 0,
          insn_lhu: 0,
          insn_sb: 0,
          insn_sh: 0,
          insn_sw: 0,
          insn_addi: 0,
          insn_slti: 0,
          insn_sltiu: 0,
          insn_xori: 0,
          insn_ori: 0,
          insn_andi: 0,
          insn_slli: 0,
          insn_srli: 0,
          insn_srai: 0,
          insn_add: 0,
          insn_sub: 0,
          insn_sll: 0,
          insn_slt: 0,
          insn_sltu: 0,
          insn_xor: 0,
          insn_srl: 0,
          insn_sra: 0,
          insn_or: 0,
          insn_and: 0,
          insn_mul: 0,
          insn_mulh: 0,
          insn_mulhsu: 0,
          insn_mulhu: 0,
          insn_div: 0,
          insn_divu: 0,
          insn_rem: 0,
          insn_remu: 0,
          insn_ecall: 0,
          insn_fence: 0
      };
    end else begin
      begin
        execute_state <= '{
            pc: decode_state.pc,
            insn: decode_state.insn,
            cycle_status: decode_state.cycle_status,

            rs1: d_insn_rs1,
            rs2: d_insn_rs2,
            rd: d_insn_rd,

            imm_u: d_imm_u,
            imm_i_sext: d_imm_i_sext,

            insn_lui: d_insn_lui,
            insn_auipc: d_insn_auipc,
            insn_jal: d_insn_jal,
            insn_jalr: d_insn_jalr,
            insn_beq: d_insn_beq,
            insn_bne: d_insn_bne,
            insn_blt: d_insn_blt,
            insn_bge: d_insn_bge,
            insn_bltu: d_insn_bltu,
            insn_bgeu: d_insn_bgeu,
            insn_lb: d_insn_lb,
            insn_lh: d_insn_lh,
            insn_lw: d_insn_lw,
            insn_lbu: d_insn_lbu,
            insn_lhu: d_insn_lhu,
            insn_sb: d_insn_sb,
            insn_sh: d_insn_sh,
            insn_sw: d_insn_sw,
            insn_addi: d_insn_addi,
            insn_slti: d_insn_slti,
            insn_sltiu: d_insn_sltiu,
            insn_xori: d_insn_xori,
            insn_ori: d_insn_ori,
            insn_andi: d_insn_andi,
            insn_slli: d_insn_slli,
            insn_srli: d_insn_srli,
            insn_srai: d_insn_srai,
            insn_add: d_insn_add,
            insn_sub: d_insn_sub,
            insn_sll: d_insn_sll,
            insn_slt: d_insn_slt,
            insn_sltu: d_insn_sltu,
            insn_xor: d_insn_xor,
            insn_srl: d_insn_srl,
            insn_sra: d_insn_sra,
            insn_or: d_insn_or,
            insn_and: d_insn_and,
            insn_mul: d_insn_mul,
            insn_mulh: d_insn_mulh,
            insn_mulhsu: d_insn_mulhsu,
            insn_mulhu: d_insn_mulhu,
            insn_div: d_insn_div,
            insn_divu: d_insn_divu,
            insn_rem: d_insn_rem,
            insn_remu: d_insn_remu,
            insn_ecall: d_insn_ecall,
            insn_fence: d_insn_fence
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

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  // // //
  // EXECUTE: Modules Used
  // // //

  logic [4:0] x_rs1, x_rd;
  logic [`REG_SIZE] x_rd_data_inter;
  logic [`REG_SIZE] x_rd_data, x_rs1_data, x_rs2_data;
  logic x_we;

  logic [`REG_SIZE] x_cla_a, x_cla_b;

  cla x_cla (
      .a  (x_cla_a),
      .b  (x_cla_b),
      .cin(1'b0),
      .sum(x_rd_data_inter)
  );

  // // //
  // EXECUTE: Logic
  // // //

  always_comb begin

    if (execute_state.insn_lui == 1) begin
      x_rd = execute_state.rd;
      x_rd_data = {execute_state.imm_u, 12'b0};
      x_we = 1;
    end else begin
      x_rd = 0;
      x_rd_data = 0;
      x_we = 1;
    end

    if (execute_state.insn_addi == 1) begin
      x_cla_a = x_rs1_data;
      x_cla_b = execute_state.imm_i_sext;

      x_rd = execute_state.rd;
      x_rd_data = x_rd_data_inter;
      x_we = 1;
    end else begin
      x_cla_a = 0;
      x_cla_b = 0;

      x_rd = 0;
      x_rd_data = 0;
      x_we = 0;
    end

    // More instructions here...

  end

  /****************/
  /* MEMORY STAGE */
  /****************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET, rd: 0, rd_data: 0, we: 0};
    end else begin
      begin
        memory_state <= '{
            pc: execute_state.pc,
            insn: execute_state.insn,
            cycle_status: execute_state.cycle_status,

            rd: x_rd,
            rd_data: x_rd_data,

            we: x_we
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

          we: memory_state.we
      };
    end else begin
      begin
        writeback_state <= '{
            pc: memory_state.pc,
            insn: memory_state.insn,
            cycle_status: memory_state.cycle_status,

            rd: memory_state.rd,
            rd_data: memory_state.rd_data,

            we: memory_state.we
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

  logic w_we;
  logic [`REG_SIZE] w_rd_data;

  always_comb begin

    if (writeback_state.we == 1) begin
      w_rd_data = writeback_state.rd_data;
      w_we = writeback_state.we;
    end else begin
      w_rd_data = 0;
      w_we = 0;
    end

    // More instructions here...

  end
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
