// Compatibility wrapper for Verilator 4.028's nested --top-module limitation.
// Original CPU source is not edited. Bus responses remain external inputs.
module pico_transfer_top (
  input clk, resetn, mem_ready,
  input [31:0] mem_rdata,
  output trap, mem_valid, mem_instr,
  output [31:0] mem_addr, mem_wdata,
  output [3:0] mem_wstrb
);
  picorv32 #(
    .COMPRESSED_ISA(0), .ENABLE_MUL(0), .ENABLE_DIV(0), .ENABLE_IRQ(0)
  ) cpu (
    .clk(clk), .resetn(resetn), .trap(trap),
    .mem_valid(mem_valid), .mem_instr(mem_instr), .mem_ready(mem_ready),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata), .irq(32'b0),
    .pcpi_wr(1'b0), .pcpi_rd(32'b0), .pcpi_wait(1'b0), .pcpi_ready(1'b0)
  );
endmodule
