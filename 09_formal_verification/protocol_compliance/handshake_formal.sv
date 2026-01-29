// Formal Properties for Valid-Ready Handshake Protocol
// This is the most common handshake protocol in digital design

module handshake_formal_properties #(
    parameter DATA_WIDTH = 32
) (
    input logic                   clk,
    input logic                   rst_n,
    
    // Valid-ready handshake
    input logic                   valid,
    input logic                   ready,
    input logic [DATA_WIDTH-1:0]  data
);

    // ============================================
    // BASIC HANDSHAKE PROTOCOL RULES
    // ============================================
    
    // Rule 1: Valid must stay high until ready (no dropping valid)
    property valid_stable_until_ready;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid;
    endproperty
    
    assert_valid_stable: assert property (valid_stable_until_ready)
        else $error("PROTOCOL VIOLATION: Valid dropped before ready asserted");
    
    // Rule 2: Data must be stable while valid && !ready
    property data_stable_until_transfer;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> $stable(data);
    endproperty
    
    assert_data_stable: assert property (data_stable_until_transfer)
        else $error("PROTOCOL VIOLATION: Data changed while valid and waiting for ready");
    
    // Rule 3: Transfer occurs when both valid and ready are high
    // This is more of a definition than a checkable property
    
    // Rule 4: Ready may be combinationally dependent on valid, but not required
    // (No property needed - this is a guideline)
    
    // ============================================
    // ADDITIONAL PROTOCOL CHECKS
    // ============================================
    
    // Property: No X or Z values on valid signal
    property valid_defined;
        @(posedge clk) disable iff (!rst_n)
        !$isunknown(valid);
    endproperty
    
    assert_valid_clean: assert property (valid_defined)
        else $error("PROTOCOL VIOLATION: Valid contains X or Z");
    
    // Property: No X or Z values on ready signal
    property ready_defined;
        @(posedge clk) disable iff (!rst_n)
        !$isunknown(ready);
    endproperty
    
    assert_ready_clean: assert property (ready_defined)
        else $error("PROTOCOL VIOLATION: Ready contains X or Z");
    
    // Property: Data must be defined when valid is asserted
    property data_defined_when_valid;
        @(posedge clk) disable iff (!rst_n)
        valid |-> !$isunknown(data);
    endproperty
    
    assert_data_clean: assert property (data_defined_when_valid)
        else $error("PROTOCOL VIOLATION: Data contains X or Z when valid");
    
    // ============================================
    // PERFORMANCE PROPERTIES
    // ============================================
    
    // Property: Ready eventually asserted (no permanent stall)
    property ready_eventually_asserted;
        @(posedge clk) disable iff (!rst_n)
        valid |-> ##[1:100] ready;
    endproperty
    
    assert_no_deadlock: assert property (ready_eventually_asserted)
        else $error("PERFORMANCE: Ready not asserted within 100 cycles");
    
    // Property: Back-to-back transfers are possible
    // (This is a coverage property to ensure protocol supports high throughput)
    sequence back_to_back_transfers;
        (valid && ready) ##1 (valid && ready);
    endsequence
    
    cover_back_to_back: cover property (@(posedge clk) back_to_back_transfers);
    
    // ============================================
    // TRANSFER COUNTING
    // ============================================
    
    // Helper: Count successful transfers
    logic [31:0] transfer_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            transfer_count <= 0;
        else if (valid && ready)
            transfer_count <= transfer_count + 1;
    end
    
    // Property: Transfers only occur when both signals high
    property transfer_definition;
        @(posedge clk) disable iff (!rst_n)
        (valid && ready) |=> (transfer_count == $past(transfer_count) + 1);
    endproperty
    
    assert_transfer_count: assert property (transfer_definition);
    
    // ============================================
    // EDGE CASE COVERAGE
    // ============================================
    
    // Cover: Valid asserted for multiple cycles before ready
    sequence valid_waits;
        valid && !ready ##1 valid && !ready ##1 valid && !ready ##1 valid && ready;
    endsequence
    
    cover_valid_waits: cover property (@(posedge clk) valid_waits);
    
    // Cover: Ready asserted before valid (speculative ready)
    sequence ready_early;
        !valid && ready ##1 valid && ready;
    endsequence
    
    cover_ready_early: cover property (@(posedge clk) ready_early);
    
    // Cover: Valid and ready assert same cycle from idle
    cover_simultaneous: cover property (
        @(posedge clk) !valid && !ready ##1 valid && ready
    );
    
    // Cover: Extended transfer burst
    sequence transfer_burst;
        (valid && ready)[*10];
    endsequence
    
    cover_burst: cover property (@(posedge clk) transfer_burst);

endmodule

// ============================================
// PIPELINED HANDSHAKE WITH SKID BUFFER
// ============================================

module skid_buffer_formal_properties #(
    parameter DATA_WIDTH = 32
) (
    input logic                   clk,
    input logic                   rst_n,
    
    // Upstream interface
    input logic                   s_valid,
    input logic                   s_ready,
    input logic [DATA_WIDTH-1:0]  s_data,
    
    // Downstream interface  
    input logic                   m_valid,
    input logic                   m_ready,
    input logic [DATA_WIDTH-1:0]  m_data,
    
    // Internal state (for checking)
    input logic                   skid_valid,
    input logic [DATA_WIDTH-1:0]  skid_data
);

    // ============================================
    // SKID BUFFER PROTOCOL
    // ============================================
    
    // Property: Upstream handshake protocol
    assert_upstream: assert property (
        @(posedge clk) disable iff (!rst_n)
        s_valid && !s_ready |=> s_valid
    ) else $error("Upstream valid dropped");
    
    assert_upstream_data: assert property (
        @(posedge clk) disable iff (!rst_n)
        s_valid && !s_ready |=> $stable(s_data)
    ) else $error("Upstream data changed");
    
    // Property: Downstream handshake protocol
    assert_downstream: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_valid && !m_ready |=> m_valid
    ) else $error("Downstream valid dropped");
    
    assert_downstream_data: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_valid && !m_ready |=> $stable(m_data)
    ) else $error("Downstream data changed");
    
    // Property: No data loss
    // If upstream transfer occurs, either immediate downstream transfer
    // or data stored in skid buffer
    property no_data_loss;
        @(posedge clk) disable iff (!rst_n)
        (s_valid && s_ready) |-> (
            (m_valid && m_ready) ||  // Immediate pass-through
            (##1 skid_valid)         // Or stored in skid
        );
    endproperty
    
    assert_no_loss: assert property (no_data_loss);
    
    // Property: Skid buffer only fills when downstream stalls
    property skid_usage;
        @(posedge clk) disable iff (!rst_n)
        (skid_valid && !$past(skid_valid)) |-> $past(m_valid && !m_ready);
    endproperty
    
    assert_skid_purpose: assert property (skid_usage);
    
    // Property: Data integrity through skid buffer
    property data_integrity;
        logic [DATA_WIDTH-1:0] saved_data;
        @(posedge clk) disable iff (!rst_n)
        (s_valid && s_ready && m_valid && !m_ready, saved_data = s_data) |=>
            (skid_data == saved_data);
    endproperty
    
    assert_data_integrity: assert property (data_integrity);

endmodule

// ============================================
// MULTI-BEAT TRANSFER PROTOCOL
// ============================================

module multi_beat_handshake_formal #(
    parameter DATA_WIDTH = 32
) (
    input logic                   clk,
    input logic                   rst_n,
    
    input logic                   valid,
    input logic                   ready,
    input logic                   last,    // Indicates last beat of burst
    input logic [DATA_WIDTH-1:0]  data,
    input logic [3:0]             beat_count  // Current beat in burst
);

    // Property: Last signal stable during transfer
    property last_stable;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> $stable(last);
    endproperty
    
    assert_last_stable: assert property (last_stable);
    
    // Property: Last eventually asserts (no infinite burst)
    property burst_terminates;
        @(posedge clk) disable iff (!rst_n)
        valid && !last |-> ##[1:256] (valid && last);
    endproperty
    
    assert_burst_ends: assert property (burst_terminates);
    
    // Property: Beat count increments with each transfer
    property beat_count_increments;
        @(posedge clk) disable iff (!rst_n)
        (valid && ready && !last) |=> (beat_count == $past(beat_count) + 1);
    endproperty
    
    assert_beat_count: assert property (beat_count_increments);
    
    // Property: Beat count resets after last
    property beat_count_reset;
        @(posedge clk) disable iff (!rst_n)
        (valid && ready && last) |=> (beat_count == 0);
    endproperty
    
    assert_count_reset: assert property (beat_count_reset);
    
    // Cover: Various burst lengths
    cover_single_beat: cover property (
        @(posedge clk) valid && ready && last && (beat_count == 0)
    );
    
    cover_four_beat: cover property (
        @(posedge clk) valid && ready && last && (beat_count == 3)
    );
    
    cover_sixteen_beat: cover property (
        @(posedge clk) valid && ready && last && (beat_count == 15)
    );

endmodule

// ============================================
// CREDIT-BASED FLOW CONTROL
// ============================================

module credit_flow_control_formal #(
    parameter MAX_CREDITS = 8
) (
    input logic clk,
    input logic rst_n,
    
    // Sender interface
    input logic send_valid,
    input logic [$clog2(MAX_CREDITS):0] credits,
    
    // Credit return
    input logic credit_return,
    input logic [$clog2(MAX_CREDITS):0] credits_returned
);

    // Property: Don't send without credits
    property respect_credits;
        @(posedge clk) disable iff (!rst_n)
        send_valid |-> (credits > 0);
    endproperty
    
    assert_have_credits: assert property (respect_credits);
    
    // Property: Credits never exceed maximum
    property credits_bounded;
        @(posedge clk) disable iff (!rst_n)
        credits <= MAX_CREDITS;
    endproperty
    
    assert_credit_limit: assert property (credits_bounded);
    
    // Property: Credits returned are reasonable
    property reasonable_return;
        @(posedge clk) disable iff (!rst_n)
        credit_return |-> (credits_returned > 0 && credits_returned <= MAX_CREDITS);
    endproperty
    
    assert_return_valid: assert property (reasonable_return);

endmodule
