// -----------------------------------------------------------------------------
// sync_fifo.sv
// Synchronous FIFO (single clock domain) - SystemVerilog
//
// Behaviour summary
//   * Push : on a rising clk edge with i_wren=1 and o_fifo_full=0,
//            i_data_in is written to mem[write_ptr] and write_ptr advances.
//   * Pull : on a rising clk edge with i_rden=1 and o_fifo_empty=0,
//            mem[read_ptr] is registered onto o_data_out (1-cycle latency)
//            and read_ptr advances.
//   * Push and pull in the same cycle are both allowed (subject to the
//     full / empty checks above).
//   * Full  : write_ptr == read_ptr - 1   (modulo FIFO_DEPTH, per spec).
//             NOTE: this "one empty slot" scheme means the FIFO holds at most
//             FIFO_DEPTH-1 entries.
//   * Empty : write_ptr == read_ptr
//
// Edge cases (per spec)
//   1. Pull when empty : o_data_out holds its value, read_ptr does not move.
//   2. Push when full  : data is dropped, write_ptr does not move.
//
// Resets
//   * ares : active-high asynchronous reset
//   * rst  : active-high synchronous reset
//   Both clear the pointers and o_data_out. Memory contents are not cleared
//   (they are unreachable until rewritten, so this saves area).
//
// FIFO_DEPTH may be any value >= 2 (power of two not required).
// -----------------------------------------------------------------------------

module sync_fifo #(
    parameter int unsigned FIFO_DEPTH      = 16,
    parameter int unsigned FIFO_DATA_WIDTH = 8
) (
    // General
    input  logic                            clk,
    input  logic                            rst,    // active-high sync reset
    input  logic                            ares,   // active-high async reset

    // Push interface
    input  logic [FIFO_DATA_WIDTH-1:0]      i_data_in,
    input  logic                            i_wren,
    output logic                            o_fifo_full,
    output logic [$clog2(FIFO_DEPTH+1)-1:0] o_fifo_count,

    // Pull interface
    input  logic                            i_rden,
    output logic [FIFO_DATA_WIDTH-1:0]      o_data_out,
    output logic                            o_fifo_empty
);

    // -------------------------------------------------------------------------
    // Local parameters
    // -------------------------------------------------------------------------
    localparam int unsigned PTR_W = (FIFO_DEPTH > 1) ? $clog2(FIFO_DEPTH) : 1;
    localparam int unsigned CNT_W = $clog2(FIFO_DEPTH + 1);

    localparam logic [PTR_W-1:0] PTR_MAX = PTR_W'(FIFO_DEPTH - 1);

    // -------------------------------------------------------------------------
    // Elaboration-time parameter check
    // -------------------------------------------------------------------------
    if (FIFO_DEPTH < 2) begin : g_bad_depth
        $error("sync_fifo: FIFO_DEPTH must be >= 2 (got %0d)", FIFO_DEPTH);
    end
    if (FIFO_DATA_WIDTH < 1) begin : g_bad_width
        $error("sync_fifo: FIFO_DATA_WIDTH must be >= 1 (got %0d)", FIFO_DATA_WIDTH);
    end

    // -------------------------------------------------------------------------
    // Storage and pointers
    // -------------------------------------------------------------------------
    logic [FIFO_DATA_WIDTH-1:0] mem [FIFO_DEPTH];

    logic [PTR_W-1:0] write_ptr, write_ptr_nxt;
    logic [PTR_W-1:0] read_ptr,  read_ptr_nxt;

    logic do_write, do_read;

    // -------------------------------------------------------------------------
    // Combinational logic: next pointers, flags, count, qualified enables
    // -------------------------------------------------------------------------
    always_comb begin
        // Wrap-around (works for non power-of-2 depths)
        write_ptr_nxt = (write_ptr == PTR_MAX) ? '0 : write_ptr + 1'b1;
        read_ptr_nxt  = (read_ptr  == PTR_MAX) ? '0 : read_ptr  + 1'b1;

        // full when write_ptr == read_ptr - 1  <=>  write_ptr + 1 == read_ptr
        o_fifo_full  = (write_ptr_nxt == read_ptr);
        o_fifo_empty = (write_ptr     == read_ptr);

        // Number of stored entries: (write_ptr - read_ptr) mod FIFO_DEPTH
        if (write_ptr >= read_ptr)
            o_fifo_count = CNT_W'(write_ptr - read_ptr);
        else
            o_fifo_count = CNT_W'(FIFO_DEPTH - read_ptr + write_ptr);

        // Ignore push when full, pull when empty
        do_write = i_wren & ~o_fifo_full;
        do_read  = i_rden & ~o_fifo_empty;
    end

    // -------------------------------------------------------------------------
    // Memory write (no reset on the array -> can infer block RAM)
    // -------------------------------------------------------------------------
    always_ff @(posedge clk) begin
        if (do_write)
            mem[write_ptr] <= i_data_in;
    end

    // -------------------------------------------------------------------------
    // Pointers and output register
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or posedge ares) begin
        if (ares) begin
            write_ptr  <= '0;
            read_ptr   <= '0;
            o_data_out <= '0;
        end else if (rst) begin
            write_ptr  <= '0;
            read_ptr   <= '0;
            o_data_out <= '0;
        end else begin
            if (do_write)
                write_ptr <= write_ptr_nxt;

            if (do_read) begin
                o_data_out <= mem[read_ptr];
                read_ptr   <= read_ptr_nxt;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Assertions (simulation only)
    //   * Excluded from synthesis.
    //   * Excluded under Icarus Verilog, which does not support concurrent
    //     assertions (it predefines __ICARUS__).
    //   * Disabled while either reset is active.
    // -------------------------------------------------------------------------
`ifndef SYNTHESIS
`ifndef __ICARUS__

    default clocking cb @(posedge clk); endclocking
    default disable iff (ares || rst);

    // Full and empty can never be true together
    a_not_full_and_empty: assert property (!(o_fifo_full && o_fifo_empty))
        else $error("sync_fifo: full and empty asserted together");

    // Count never exceeds usable capacity (FIFO_DEPTH-1, one slot kept empty)
    a_count_in_range: assert property (o_fifo_count <= FIFO_DEPTH - 1)
        else $error("sync_fifo: count %0d exceeds capacity %0d",
                    o_fifo_count, FIFO_DEPTH - 1);

    // Flags agree with the count
    a_empty_matches_count: assert property (o_fifo_empty == (o_fifo_count == 0))
        else $error("sync_fifo: empty flag disagrees with count");
    a_full_matches_count: assert property (o_fifo_full == (o_fifo_count == FIFO_DEPTH - 1))
        else $error("sync_fifo: full flag disagrees with count");

    // Edge case 2: push when full is dropped (write_ptr holds)
    a_no_push_when_full: assert property (i_wren && o_fifo_full |=> $stable(write_ptr))
        else $error("sync_fifo: write_ptr moved on push while full");

    // Edge case 1: pull when empty is ignored (read_ptr and o_data_out hold)
    a_no_pull_when_empty: assert property (i_rden && o_fifo_empty |=> $stable(read_ptr) && $stable(o_data_out))
        else $error("sync_fifo: read_ptr/o_data_out changed on pull while empty");

    // Count tracks accepted pushes and pulls
    a_count_inc: assert property (do_write && !do_read |=> o_fifo_count == $past(o_fifo_count) + 1)
        else $error("sync_fifo: count did not increment on push");
    a_count_dec: assert property (!do_write && do_read |=> o_fifo_count == $past(o_fifo_count) - 1)
        else $error("sync_fifo: count did not decrement on pull");
    a_count_hold: assert property (do_write == do_read |=> $stable(o_fifo_count))
        else $error("sync_fifo: count changed with no net push/pull");

`endif // __ICARUS__
`endif // SYNTHESIS

endmodule
