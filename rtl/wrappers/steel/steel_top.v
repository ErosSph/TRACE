// Environment wrapper for the (unmodified) Steel core rvx_core.v, pinned riscv-steel @ 7af8290a.
// proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0.
//
// ENVIRONMENT (not design): a 512-byte unified single-port synchronous memory, behaviourally the same as
// rvx_ram.v (read_data registered, read_response/write_response = request delayed one cycle, byte write
// strobes, address >= 512 reads 0, memory zero on reset reads) with rvx_bus.v's single device collapsed
// (the bus with one device whose region covers the memory is the identity except that, for addresses
// outside the region, responses are forced to 1; the verification domain never leaves the image).
// The memory contents are the program image, seeded as initial state of `ram`.
// Tied inputs: halt=0, irq_external=irq_timer=irq_software=0, irq_fast=0, real_time_clock=0.
// Parameter: BOOT_ADDRESS=0 (default).
module steel_top (
  input wire clock,
  input wire reset
);
  wire [31:0] rw_address;
  wire        read_request;
  wire [31:0] write_data;
  wire [3:0]  write_strobe;
  wire        write_request;
  wire        irq_external_response, irq_timer_response, irq_software_response;
  wire [15:0] irq_fast_response;

  reg  [31:0] read_data;
  reg         read_response;
  reg         write_response;
  reg         env_reset_reg;
  reg  [31:0] ram [0:127];

  wire        env_reset;
  wire        invalid_address;
  wire [6:0]  word_index;

  assign env_reset       = reset | env_reset_reg;
  assign invalid_address = rw_address >= 32'd512;
  assign word_index      = rw_address[8:2];

  always @(posedge clock)
    env_reset_reg <= reset;

  always @(posedge clock) begin
    if (env_reset | invalid_address)
      read_data <= 32'h00000000;
    else
      read_data <= ram[word_index];
  end

  always @(posedge clock) begin
    if (write_request && !invalid_address) begin
      if (write_strobe[0]) ram[word_index][7:0]   <= write_data[7:0];
      if (write_strobe[1]) ram[word_index][15:8]  <= write_data[15:8];
      if (write_strobe[2]) ram[word_index][23:16] <= write_data[23:16];
      if (write_strobe[3]) ram[word_index][31:24] <= write_data[31:24];
    end
  end

  always @(posedge clock) begin
    if (env_reset) begin
      read_response  <= 1'b0;
      write_response <= 1'b0;
    end else begin
      read_response  <= read_request;
      write_response <= write_request;
    end
  end

  rvx_core #(.BOOT_ADDRESS(32'h00000000)) core (
    .clock(clock), .reset(reset), .halt(1'b0),
    .rw_address(rw_address), .read_data(read_data), .read_request(read_request),
    .read_response(read_response), .write_data(write_data), .write_strobe(write_strobe),
    .write_request(write_request), .write_response(write_response),
    .irq_external(1'b0), .irq_external_response(irq_external_response),
    .irq_timer(1'b0), .irq_timer_response(irq_timer_response),
    .irq_software(1'b0), .irq_software_response(irq_software_response),
    .irq_fast(16'h0000), .irq_fast_response(irq_fast_response),
    .real_time_clock(64'h0));
endmodule
