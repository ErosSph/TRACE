// Verification top (environment model) for AngeloJacobo/RISC-V rv32i_core (pin b0ab0550).
// The core RTL (rtl/rv32i_*.v) is NOT modified; this file only models the environment.
//
// The memory below is a faithful extract of `main_memory` from the project's own SoC (test/rv32i_soc.v):
//  - one combined instruction/data memory of MEMORY_DEPTH bytes (512 -> 128 words), word array, addresses alias modulo 512;
//  - registered reads: o_inst_out/o_wb_data take the word one cycle after the address; o_ack_inst <= i_stb_inst;
//    o_wb_ack <= i_wb_stb && i_wb_cyc; o_wb_stall = 0 (never stall); byte-lane writes from i_wb_sel.
// Not modelled (SoC parts): bus decoder, CLINT, UART, I2C, GPIO, SPI/LCD. Interrupt inputs tied inactive.
// Initial memory content (the program image) and the all-zero initial register/pipeline state are supplied by the
// simulation seed (the image is the initial value of `mem`; no `initial` blocks are used).
// Parameters: PC_RESET=0, TRAP_ADDRESS=0, ZICSR_EXTENSION=1 (the core's defaults).
`timescale 1ns / 1ps
`default_nettype none
module angelo5_top (
    input wire i_clk,
    input wire i_rst_n
);
    reg [31:0] mem [0:127];
    wire [31:0] iaddr;
    wire stb_inst;
    reg ack_inst;
    reg [31:0] inst;
    wire wb_cyc, wb_stb, wb_we;
    wire [31:0] wb_addr, wb_wdata;
    wire [3:0] wb_sel;
    reg wb_ack;
    reg [31:0] wb_rdata;

    rv32i_core #(.PC_RESET(32'h00000000), .TRAP_ADDRESS(0), .ZICSR_EXTENSION(1)) core (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .i_inst(inst), .o_iaddr(iaddr), .o_stb_inst(stb_inst), .i_ack_inst(ack_inst),
        .o_wb_cyc_data(wb_cyc), .o_wb_stb_data(wb_stb), .o_wb_we_data(wb_we),
        .o_wb_addr_data(wb_addr), .o_wb_data_data(wb_wdata), .o_wb_sel_data(wb_sel),
        .i_wb_ack_data(wb_ack), .i_wb_stall_data(1'b0), .i_wb_data_data(wb_rdata),
        .i_external_interrupt(1'b0), .i_software_interrupt(1'b0), .i_timer_interrupt(1'b0)
    );

    always @(posedge i_clk) begin
        ack_inst <= stb_inst;
        wb_ack <= wb_stb && wb_cyc;
        inst <= mem[iaddr[8:2]];
        wb_rdata <= mem[wb_addr[8:2]];
    end

    always @(posedge i_clk) begin
        if (wb_we && wb_stb && wb_cyc) begin
            if (wb_sel[0]) mem[wb_addr[8:2]][7:0] <= wb_wdata[7:0];
            if (wb_sel[1]) mem[wb_addr[8:2]][15:8] <= wb_wdata[15:8];
            if (wb_sel[2]) mem[wb_addr[8:2]][23:16] <= wb_wdata[23:16];
            if (wb_sel[3]) mem[wb_addr[8:2]][31:24] <= wb_wdata[31:24];
        end
    end
endmodule
