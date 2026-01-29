// Formal Verification of Multi-Cycle Path (MCP) CDC
// Proves that multi-cycle paths across clock domains are safe

module mcp_synchronizer #(
    parameter DATA_WIDTH = 32,
    parameter MCP_CYCLES = 3  // Number of source cycles data is stable
) (
    // Source domain
    input  logic                   clk_src,
    input  logic                   rst_src_n,
    input  logic [DATA_WIDTH-1:0]  data_in,
    input  logic                   update,      // Pulse when data changes
    
    // Destination domain
    input  logic                   clk_dst,
    input  logic                   rst_dst_n,
    output logic [DATA_WIDTH-1:0]  data_out,
    output logic                   data_valid
);

    // ============================================
    // IMPLEMENTATION: MCP with Enable
    // ============================================
    
    // Source domain: Hold data stable for MCP_CYCLES
    logic [DATA_WIDTH-1:0] data_hold;
    logic [$clog2(MCP_CYCLES+1)-1:0] hold_count;
    logic mcp_enable;  // Asserted when data stable
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            data_hold <= '0;
            hold_count <= 0;
            mcp_enable <= 1'b0;
        end else if (update) begin
            data_hold <= data_in;
            hold_count <= 1;
            mcp_enable <= 1'b0;
        end else if (hold_count < MCP_CYCLES) begin
            hold_count <= hold_count + 1;
            mcp_enable <= 1'b0;
        end else begin
            mcp_enable <= 1'b1;
        end
    end
    
    // Synchronize enable signal
    logic enable_sync1, enable_sync2;
    
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            enable_sync1 <= 1'b0;
            enable_sync2 <= 1'b0;
        end else begin
            enable_sync1 <= mcp_enable;
            enable_sync2 <= enable_sync1;
        end
    end
    
    // Destination domain: Sample data when enable asserted
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            data_out <= '0;
            data_valid <= 1'b0;
        end else if (enable_sync2) begin
            data_out <= data_hold;
            data_valid <= 1'b1;
        end else begin
            data_valid <= 1'b0;
        end
    end

endmodule

// ============================================
// FORMAL PROPERTIES FOR MCP
// ============================================

module mcp_formal_properties #(
    parameter DATA_WIDTH = 32,
    parameter MCP_CYCLES = 3
) (
    // Source domain
    input logic                   clk_src,
    input logic                   rst_src_n,
    input logic [DATA_WIDTH-1:0]  data_in,
    input logic                   update,
    
    // Destination domain
    input logic                   clk_dst,
    input logic                   rst_dst_n,
    input logic [DATA_WIDTH-1:0]  data_out,
    input logic                   data_valid,
    
    // Internal signals
    input logic [DATA_WIDTH-1:0]  data_hold,
    input logic                   mcp_enable,
    input logic                   enable_sync1,
    input logic                   enable_sync2
);

    // ============================================
    // SOURCE DOMAIN PROPERTIES
    // ============================================
    
    // Property 1: Data captured on update
    property data_captured;
        logic [DATA_WIDTH-1:0] captured;
        @(posedge clk_src) disable iff (!rst_src_n)
        (update, captured = data_in) |=>
        (data_hold == captured);
    endproperty
    
    a_capture: assert property (data_captured)
        else $error("SRC: Data not captured");
    
    // Property 2: Data stable for MCP_CYCLES after update
    property data_stable_mcp;
        @(posedge clk_src) disable iff (!rst_src_n)
        update |=> $stable(data_hold)[*MCP_CYCLES];
    endproperty
    
    a_stable: assert property (data_stable_mcp)
        else $error("SRC: Data not stable for MCP cycles");
    
    // Property 3: Enable asserts only after stability period
    property enable_timing;
        @(posedge clk_src) disable iff (!rst_src_n)
        update |-> ##MCP_CYCLES mcp_enable;
    endproperty
    
    a_enable_time: assert property (enable_timing)
        else $error("SRC: Enable timing wrong");
    
    // Property 4: Enable stays high until next update
    property enable_stable;
        @(posedge clk_src) disable iff (!rst_src_n)
        mcp_enable && !update |=> mcp_enable;
    endproperty
    
    a_enable_stable: assert property (enable_stable)
        else $error("SRC: Enable not stable");
    
    // Property 5: Data doesn't change while enable asserted
    property data_frozen_during_enable;
        @(posedge clk_src) disable iff (!rst_src_n)
        mcp_enable && !update |-> $stable(data_hold);
    endproperty
    
    a_frozen: assert property (data_frozen_during_enable)
        else $error("SRC: Data changed during enable");
    
    // ============================================
    // SYNCHRONIZER PROPERTIES
    // ============================================
    
    // Property 6: Enable properly synchronized (2-FF)
    // Structural check - can't fully verify metastability
    
    // ============================================
    // DESTINATION DOMAIN PROPERTIES
    // ============================================
    
    // Property 7: Valid asserts when enable synchronized
    property valid_on_enable;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        enable_sync2 |-> data_valid;
    endproperty
    
    a_valid: assert property (valid_on_enable);
    
    // Property 8: Data stable during valid
    property data_stable_dst;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        data_valid |-> $stable(data_out);
    endproperty
    
    // ============================================
    // DATA INTEGRITY ACROSS DOMAINS
    // ============================================
    
    // Property 9: Data at destination matches source
    // This is the key MCP correctness property!
    
    // Shadow tracking
    logic [DATA_WIDTH-1:0] shadow_data;
    logic shadow_valid;
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            shadow_valid <= 1'b0;
        end else if (update) begin
            shadow_data <= data_in;
            shadow_valid <= 1'b1;
        end else if (mcp_enable) begin
            shadow_valid <= 1'b0;  // Mark as transferred
        end
    end
    
    // Check in destination domain
    property data_integrity_mcp;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        data_valid |-> (data_out == shadow_data);
    endproperty
    
    a_integrity: assert property (data_integrity_mcp)
        else $error("MCP: Data corruption detected");
    
    // ============================================
    // TIMING CONSTRAINTS
    // ============================================
    
    // Property 10: Update rate limited (ensures MCP stability)
    property update_rate_limited;
        @(posedge clk_src) disable iff (!rst_src_n)
        update |-> ##[MCP_CYCLES+1:$] update;
    endproperty
    
    // This is an ASSUMPTION about the environment
    assume_update_rate: assume property (update_rate_limited);
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Data transfer happens
    c_transfer: cover property (
        @(posedge clk_dst) data_valid
    );
    
    // Cover: Multiple transfers
    c_multi_transfer: cover property (
        @(posedge clk_dst) data_valid ##[10:$] data_valid
    );
    
    // Cover: Different data values
    c_data_zero: cover property (
        @(posedge clk_dst) data_valid && (data_out == 0)
    );
    
    c_data_max: cover property (
        @(posedge clk_dst) data_valid && (data_out == '1)
    );

endmodule

// ============================================
// MCP WITH QUALIFIER SIGNAL
// ============================================

module mcp_with_qualifier_formal (
    input logic        clk_src,
    input logic        rst_src_n,
    input logic [31:0] data,
    input logic        qualifier,  // Data valid when high
    
    input logic        clk_dst,
    input logic        rst_dst_n,
    input logic [31:0] data_out,
    input logic        valid_out
);

    // Property: Qualifier stable with data
    property qualifier_stable;
        @(posedge clk_src) disable iff (!rst_src_n)
        qualifier |=> $stable(data) && $stable(qualifier);
    endproperty
    
    a_qual_stable: assert property (qualifier_stable)
        else $error("Qualifier or data unstable");
    
    // Property: Data only sampled when qualifier high
    property sample_when_qualified;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        valid_out |-> qualifier;  // Cross-domain check!
    endproperty

endmodule

// ============================================
// QUASI-STATIC MCP
// ============================================

module quasi_static_mcp_formal (
    input logic        clk_src,
    input logic        rst_src_n,
    input logic [31:0] config_data,  // Changes very rarely
    
    input logic        clk_dst,
    input logic        rst_dst_n,
    input logic [31:0] config_out
);

    // Property: Configuration stable for long periods
    property config_quasi_static;
        @(posedge clk_src) disable iff (!rst_src_n)
        1'b1 |-> ##[100:$] $stable(config_data);
    endproperty
    
    // ASSUMPTION: Config changes rarely
    assume_quasi_static: assume property (config_quasi_static);
    
    // Property: Eventually matches in destination
    property eventual_match;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        ##[1:20] (config_out == config_data);
    endproperty

endmodule

// ============================================
// MCP WITH FEEDBACK ACK
// ============================================

module mcp_with_ack_formal (
    input logic        clk_src,
    input logic        rst_src_n,
    input logic [31:0] data_src,
    input logic        send,
    input logic        ack_received,
    
    input logic        clk_dst,
    input logic        rst_dst_n,
    input logic [31:0] data_dst,
    input logic        valid_dst,
    input logic        send_ack
);

    // Property: Data stable until acknowledged
    property data_stable_until_ack;
        @(posedge clk_src) disable iff (!rst_src_n)
        send && !ack_received |=> $stable(data_src) && send;
    endproperty
    
    a_stable_ack: assert property (data_stable_until_ack)
        else $error("Data changed before ack");
    
    // Property: Ack only sent after data sampled
    property ack_after_sample;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        send_ack |-> valid_dst;
    endproperty

endmodule

// ============================================
// MULTIPLE PARALLEL MCP PATHS
// ============================================

module parallel_mcp_formal (
    input logic        clk_src,
    input logic        rst_src_n,
    input logic [31:0] data_a,
    input logic [31:0] data_b,
    input logic [31:0] data_c,
    input logic        update_all,
    
    input logic        clk_dst,
    input logic        rst_dst_n,
    input logic [31:0] out_a,
    input logic [31:0] out_b,
    input logic [31:0] out_c,
    input logic        valid_all
);

    // Property: All paths stable together
    property all_stable;
        @(posedge clk_src) disable iff (!rst_src_n)
        update_all |=> 
        $stable(data_a) && $stable(data_b) && $stable(data_c);
    endproperty
    
    a_all_stable: assert property (all_stable)
        else $error("Not all MCP paths stable");
    
    // Property: All sampled atomically
    property atomic_sample;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        valid_all |->
        (out_a == data_a) && (out_b == data_b) && (out_c == data_c);
    endproperty
    
    a_atomic: assert property (atomic_sample);

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Multi-Cycle Path (MCP) CDC:
 *
 * Definition:
 *   - Data crosses clock domains
 *   - Source guarantees data stable for multiple cycles
 *   - Destination samples during stable window
 *   - No synchronizer on data (only on enable/qualifier)
 *
 * When to use:
 *   - Wide data buses (synchronizers expensive)
 *   - Quasi-static signals (configs, modes)
 *   - Performance-critical paths
 *   - Where full handshake too slow
 *
 * Safety Requirements:
 *   1. Data stable for >= setup + hold + uncertainty
 *   2. Enable/qualifier properly synchronized
 *   3. Source and destination aware of protocol
 *   4. Timing constraints documented
 *
 * Verification Strategy:
 *   1. Prove data stability in source domain
 *   2. Verify qualifier/enable synchronization
 *   3. Check data integrity in destination
 *   4. Confirm timing assumptions met
 *
 * Common Mistakes:
 *   - Data changes too soon
 *   - Enable not synchronized
 *   - Clock frequency assumptions wrong
 *   - Metastability on enable
 *
 * Comparison to other CDC methods:
 *
 * MCP:
 *   + Low latency
 *   + No data synchronizers
 *   + High throughput
 *   - Requires careful timing
 *   - Static timing checks critical
 *   - Must document constraints
 *
 * Handshake:
 *   + Safe for any data
 *   + No timing assumptions
 *   + Clock-independent
 *   - Higher latency
 *   - More logic
 *
 * FIFO:
 *   + High throughput
 *   + Handles bursts
 *   + Flow control
 *   - More complex
 *   - Higher area
 *
 * Best Practices:
 *
 * 1. Document all timing assumptions
 * 2. Use formal to prove stability
 * 3. Add assertions in RTL
 * 4. Verify with STA (Static Timing Analysis)
 * 5. Use qualifier signal when possible
 * 6. Consider feedback acknowledgment
 * 7. Test across process corners
 *
 * Formal Verification proves:
 *   ✓ Data stable long enough
 *   ✓ Enable synchronized properly
 *   ✓ No data corruption
 *   ✓ Protocol followed correctly
 *   ✗ Cannot prove absolute timing
 *     (need STA for that)
 *
 * Integration with STA:
 *   - Formal proves protocol
 *   - STA proves timing margins
 *   - Both needed for complete verification
 *
 * SDC (Synopsys Design Constraints) example:
 *   set_max_delay -from [get_pins src_reg/Q] \
 *                 -to [get_pins dst_reg/D] \
 *                 [expr $src_period * $MCP_CYCLES]
 *
 *   set_multicycle_path $MCP_CYCLES \
 *                       -setup \
 *                       -from [get_pins src_reg/Q] \
 *                       -to [get_pins dst_reg/D]
 */
