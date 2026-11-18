// Verification top for NERV (datasets/nerv/nerv.sv, unmodified).  This file is ENVIRONMENT, not design.
// proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
//
// Choices (all documented in proof-optimization-log/20261104-nerv-import.md):
//  * nerv parameters fixed: RESET_ADDR = 0, NUMREGS = 32 (the upstream defaults, written explicitly).
//  * stall = 0 (no external stall), irq = 0 (no interrupt), imem_fault/dmem_fault do not exist
//    (NERV_FAULT is not defined, so nerv ties them to 0 itself).
//  * NERV_RVFI is not defined: the RVFI monitor ports are not compiled, i.e. they are "tied off" by
//    absence.  RVFI is a verification-side monitor; it does not drive any architectural state.
//  * Instruction memory: a read-only image of 128 words (rom, seeded by the harness exactly like the Bzeeno
//    ROM).  NERV expects a SYNCHRONOUS instruction port: imem_data in cycle t is rom[imem_addr of cycle t-1]
//    (the upstream testbench registers imem_data the same way).  Fetches above word 127 wrap (index = addr[8:2]);
//    the program domain only reaches addresses inside the image.
//  * Data memory: one 32-bit word at byte address 0 (like the DarkRISCV model), synchronous read,
//    byte-lane writes.  Accesses to other addresses read 0 and write nothing; the program domain
//    restricts loads/stores to address 0 (the jump-family phase A domain has no loads/stores at all).
//  * Reset: the harness drives reset = 1 over a clock edge, then releases it.
module nerv_top (
	input clock,
	input reset
);
	reg [31:0] rom [0:127];
	reg [31:0] ram0;
	reg [31:0] imem_data;
	reg [31:0] dmem_rdata;

	wire        trap;
	wire [31:0] imem_addr;
	wire        dmem_valid;
	wire [31:0] dmem_addr;
	wire [ 3:0] dmem_wstrb;
	wire [31:0] dmem_wdata;

	nerv #(.RESET_ADDR(32'h00000000), .NUMREGS(32)) uut (
		.clock(clock),
		.reset(reset),
		.stall(1'b0),
		.trap(trap),
		.imem_addr(imem_addr),
		.imem_data(imem_data),
		.dmem_valid(dmem_valid),
		.dmem_addr(dmem_addr),
		.dmem_wstrb(dmem_wstrb),
		.dmem_wdata(dmem_wdata),
		.dmem_rdata(dmem_rdata),
		.irq(32'b0)
	);

	wire dmem_hit = dmem_valid && (dmem_addr[31:2] == 30'b0);

	always @(posedge clock) begin
		imem_data <= rom[imem_addr[8:2]];
		dmem_rdata <= dmem_hit ? ram0 : 32'b0;
		if (dmem_hit && dmem_wstrb[0]) ram0[7:0]   <= dmem_wdata[7:0];
		if (dmem_hit && dmem_wstrb[1]) ram0[15:8]  <= dmem_wdata[15:8];
		if (dmem_hit && dmem_wstrb[2]) ram0[23:16] <= dmem_wdata[23:16];
		if (dmem_hit && dmem_wstrb[3]) ram0[31:24] <= dmem_wdata[31:24];
	end
endmodule
