// Verification top for kuopinghsu/srv32 (riscv.v unchanged, pinned 7129bdcf).  ENVIRONMENT, not design.
//
// Environment choices (all documented in proof-optimization-log/20261104-srv32-import.md):
//  * instruction memory: read-only ROM image `rom` (128 words, input) with the SAME timing as the upstream
//    testbench memory (testbench/memmodel.v mem2ports): synchronous read, `rdata <= ram[raddr]` when
//    imem_ready & imem_valid; addresses outside the 512-byte image read 0 (upstream zero-initialises RAM).
//  * imem_valid = 1, imem_rresp = 1 (upstream: imem_valid = 1; rresp unused by riscv.v for imem).
//  * data memory is absent: dmem_rvalid = dmem_wvalid = dmem_rresp = 1, dmem_rdata = 0.  The jump-family domain
//    has no loads/stores, so these inputs are never used by a committed instruction.
//  * stall = 0, interrupt = timer_irq = sw_irq = 0 (inactive).  The CLINT of top.v is not instantiated.
//  * parameters RV32M = 0, RV32E = 0, RV32B = 0, RV32C = 0 (RV32I base).
module srv32_env (
    input                   clk,
    input                   resetb,
    input  [128*32-1:0]     rom,
    output                  exception,
    output          [31: 0] imem_addr,
    output                  imem_ready,
    output          [31: 0] dmem_raddr,
    output          [31: 0] dmem_waddr,
    output          [31: 0] dmem_wdata,
    output          [ 3: 0] dmem_wstrb,
    output                  dmem_rready,
    output                  dmem_wready
);
    reg  [31:0] imem_rdata;
    wire [31:0] rom_word = rom[{imem_addr[8:2], 5'b00000} +: 32];

    always @(posedge clk) begin
        if (imem_ready)
            imem_rdata <= (imem_addr[31:9] == 23'd0) ? rom_word : 32'h0;
    end

    riscv #(.RV32M(0), .RV32E(0), .RV32B(0), .RV32C(0)) riscv (
        .clk(clk), .resetb(resetb),
        .stall(1'b0), .exception(exception), .timer_en(),
        .timer_irq(1'b0), .sw_irq(1'b0), .interrupt(1'b0),
        .imem_ready(imem_ready), .imem_valid(1'b1), .imem_addr(imem_addr),
        .imem_rresp(1'b1), .imem_rdata(imem_rdata),
        .dmem_wready(dmem_wready), .dmem_wvalid(1'b1), .dmem_waddr(dmem_waddr),
        .dmem_wdata(dmem_wdata), .dmem_wstrb(dmem_wstrb),
        .dmem_rready(dmem_rready), .dmem_rvalid(1'b1), .dmem_raddr(dmem_raddr),
        .dmem_rresp(1'b1), .dmem_rdata(32'h0)
    );
endmodule
