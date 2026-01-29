// Formal Verification of CDC Handshake Synchronizer
// Proves safe multi-bit data crossing between clock domains

module handshake_synchronizer #(
    parameter DATA_WIDTH = 32
) (
    // Source domain
    input  logic                   clk_src,
    input  logic                   rst_src_n,
    input  logic [DATA_WIDTH-1:0]  data_in,
    input  logic                   data_valid,
    output logic                   data_ack,
    
    // Destination domain
    input  logic                   clk_dst,
    input  logic                   rst_dst_n,
    output logic [DATA_WIDTH-1:0]  data_out,
    output logic                   data_ready,
    input  logic                   data_taken
);

    // ============================================
    // IMPLEMENTATION
    // ============================================
    
    // Source domain: Request signal
    logic req_src;
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n)
            req_src <= 1'b0;
        else if (data_valid && !req_src)
            req_src <= 1'b1;
        else if (data_ack)
            req_src <= 1'b0;
    end
    
    // Source domain: Data register
    logic [DATA_WIDTH-1:0] data_reg;
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n)
            data_reg <= '0;
        else if (data_valid && !req_src)
            data_reg <= data_in;
    end
    
    // Cross to destination: Synchronize req
    logic req_sync1, req_sync2;
    
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            req_sync1 <= 1'b0;
            req_sync2 <= 1'b0;
        end else begin
            req_sync1 <= req_src;
            req_sync2 <= req_sync1;
        end
    end
    
    // Destination domain: Acknowledge
    logic ack_dst;
    
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n)
            ack_dst <= 1'b0;
        else if (req_sync2 && !ack_dst)
            ack_dst <= 1'b1;
        else if (!req_sync2)
            ack_dst <= 1'b0;
    end
    
    // Cross back to source: Synchronize ack
    logic ack_sync1, ack_sync2;
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            ack_sync1 <= 1'b0;
            ack_sync2 <= 1'b0;
        end else begin
            ack_sync1 <= ack_dst;
            ack_sync2 <= ack_sync1;
        end
    end
    
    // Outputs
    assign data_ack = ack_sync2;
    assign data_out = data_reg;  // Data stable during handshake
    assign data_ready = req_sync2 && !ack_dst;

endmodule

// ============================================
// FORMAL PROPERTIES FOR CDC HANDSHAKE
// ============================================

module handshake_sync_formal_properties #(
    parameter DATA_WIDTH = 32
) (
    // Source domain
    input logic                   clk_src,
    input logic                   rst_src_n,
    input logic [DATA_WIDTH-1:0]  data_in,
    input logic                   data_valid,
    input logic                   data_ack,
    
    // Destination domain
    input logic                   clk_dst,
    input logic                   rst_dst_n,
    input logic [DATA_WIDTH-1:0]  data_out,
    input logic                   data_ready,
    input logic                   data_taken,
    
    // Internal signals (for checking)
    input logic                   req_src,
    input logic                   req_sync1,
    input logic                   req_sync2,
    input logic                   ack_dst,
    input logic                   ack_sync1,
    input logic                   ack_sync2,
    input logic [DATA_WIDTH-1:0]  data_reg
);

    // ============================================
    // SOURCE DOMAIN PROPERTIES
    // ============================================
    
    // Property 1: Request asserts when data valid
    property req_on_valid;
        @(posedge clk_src) disable iff (!rst_src_n)
        data_valid && !req_src |=> req_src;
    endproperty
    
    a_req_assert: assert property (req_on_valid);
    
    // Property 2: Request stays high until acknowledged
    property req_stable;
        @(posedge clk_src) disable iff (!rst_src_n)
        req_src && !data_ack |=> req_src;
    endproperty
    
    a_req_stable: assert property (req_stable)
        else $error("SRC: Request dropped before ack");
    
    // Property 3: Data captured when valid
    property data_captured;
        logic [DATA_WIDTH-1:0] captured;
        @(posedge clk_src) disable iff (!rst_src_n)
        (data_valid && !req_src, captured = data_in) |=>
        (data_reg == captured);
    endproperty
    
    a_data_cap: assert property (data_captured)
        else $error("SRC: Data not captured correctly");
    
    // Property 4: Data stable during handshake
    property data_stable_during_hs;
        @(posedge clk_src) disable iff (!rst_src_n)
        req_src && !data_ack |=> $stable(data_reg);
    endproperty
    
    a_data_stable_src: assert property (data_stable_during_hs)
        else $error("SRC: Data changed during handshake");
    
    // ============================================
    // SYNCHRONIZER PROPERTIES
    // ============================================
    
    // Property 5: Two-FF synchronizer for req
    // (Metastability can't be formally verified, but structure can)
    
    // Property 6: No combinational path through synchronizer
    // This is a structural check - would need hierarchical assertion
    
    // ============================================
    // DESTINATION DOMAIN PROPERTIES
    // ============================================
    
    // Property 7: Data ready when request synchronized
    property ready_on_req;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        req_sync2 && !ack_dst |-> data_ready;
    endproperty
    
    a_ready: assert property (ready_on_req);
    
    // Property 8: Acknowledge asserts when ready
    property ack_on_ready;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        data_ready && !ack_dst |=> ack_dst;
    endproperty
    
    a_ack_assert: assert property (ack_on_ready);
    
    // Property 9: Data output stable while ready
    property data_stable_dst;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        data_ready |-> $stable(data_out);
    endproperty
    
    a_data_stable_dst: assert property (data_stable_dst)
        else $error("DST: Data changed while ready");
    
    // ============================================
    // DATA INTEGRITY ACROSS DOMAINS
    // ============================================
    
    // Property 10: Data at destination matches source
    // This is the critical CDC data integrity property!
    
    // Shadow tracking in source domain
    logic [DATA_WIDTH-1:0] shadow_data;
    logic shadow_valid;
    
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            shadow_valid <= 1'b0;
        end else if (data_valid && !req_src) begin
            shadow_data <= data_in;
            shadow_valid <= 1'b1;
        end else if (data_ack) begin
            shadow_valid <= 1'b0;
        end
    end
    
    // Check in destination domain (crossing clock domains in assertion!)
    property data_integrity_cdc;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        data_ready |-> (data_out == shadow_data);
    endproperty
    
    a_data_integrity: assert property (data_integrity_cdc)
        else $error("CDC DATA ERROR: sent=%h received=%h",
                   shadow_data, data_out);
    
    // ============================================
    // FOUR-PHASE HANDSHAKE PROTOCOL
    // ============================================
    
    // Phase 1: req rises (source)
    // Phase 2: ack rises (destination)
    // Phase 3: req falls (source)
    // Phase 4: ack falls (destination)
    
    // Property 11: Ack doesn't rise before req synchronized
    property ack_after_req;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        $rose(ack_dst) |-> req_sync2;
    endproperty
    
    a_ack_order: assert property (ack_after_req);
    
    // Property 12: Req doesn't fall before ack synchronized
    property req_waits_for_ack;
        @(posedge clk_src) disable iff (!rst_src_n)
        $fell(req_src) |-> data_ack;
    endproperty
    
    a_req_order: assert property (req_waits_for_ack);
    
    // ============================================
    // LIVENESS PROPERTIES
    // ============================================
    
    // Property 13: Request eventually acknowledged
    property eventual_ack_src;
        @(posedge clk_src) disable iff (!rst_src_n)
        req_src |-> ##[1:100] data_ack;
    endproperty
    
    a_liveness_src: assert property (eventual_ack_src)
        else $error("LIVENESS: Request not acknowledged");
    
    // Property 14: Ready eventually asserts in destination
    property eventual_ready_dst;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        req_sync2 |-> ##[1:20] data_ready;
    endproperty
    
    a_liveness_dst: assert property (eventual_ready_dst);
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Complete handshake
    c_complete_hs_src: cover property (
        @(posedge clk_src) data_valid ##[1:$] data_ack
    );
    
    c_complete_hs_dst: cover property (
        @(posedge clk_dst) data_ready ##[1:$] data_taken
    );
    
    // Cover: Back-to-back transfers
    c_back_to_back_src: cover property (
        @(posedge clk_src) data_ack ##[1:5] data_valid
    );
    
    // Cover: Data values transferred
    c_data_zero: cover property (
        @(posedge clk_dst) data_ready && (data_out == 0)
    );
    
    c_data_max: cover property (
        @(posedge clk_dst) data_ready && (data_out == '1)
    );

endmodule

// ============================================
// PULSE SYNCHRONIZER (Simpler CDC)
// ============================================

module pulse_sync_formal (
    input logic clk_src,
    input logic rst_src_n,
    input logic pulse_in,
    
    input logic clk_dst,
    input logic rst_dst_n,
    input logic pulse_out,
    
    // Internal
    input logic toggle_src,
    input logic toggle_sync1,
    input logic toggle_sync2,
    input logic toggle_prev
);

    // Property: Each pulse in creates pulse out
    // This is challenging to prove across clock domains!
    
    // In source domain: pulse creates toggle
    property pulse_to_toggle;
        @(posedge clk_src) disable iff (!rst_src_n)
        pulse_in |=> (toggle_src != $past(toggle_src));
    endproperty
    
    a_src_toggle: assert property (pulse_to_toggle);
    
    // In destination: toggle creates pulse
    property toggle_to_pulse;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        (toggle_sync2 != toggle_prev) == pulse_out;
    endproperty
    
    a_dst_pulse: assert property (toggle_to_pulse);
    
    // Property: Pulse is one cycle only
    property pulse_single_cycle;
        @(posedge clk_dst) disable iff (!rst_dst_n)
        pulse_out |=> !pulse_out;
    endproperty
    
    a_pulse_width: assert property (pulse_single_cycle);

endmodule

// ============================================
// CDC VERIFICATION CHALLENGES
// ============================================

/*
 * CDC Formal Verification is challenging because:
 *
 * 1. ASYNCHRONOUS SAMPLING
 *    - Destination samples source at arbitrary time
 *    - Can't predict exact timing
 *    - Metastability can't be modeled
 *
 * 2. MULTIPLE CLOCK DOMAINS
 *    - Formal tools handle single clock best
 *    - Need special CDC formal tools
 *    - Or abstract to single clock view
 *
 * 3. CONVERGENCE
 *    - Synchronizers add latency
 *    - Need deeper traces
 *    - State space grows
 *
 * Solutions:
 *
 * 1. ABSTRACT CLOCKS
 *    - Assume arbitrary phase relationship
 *    - Focus on protocol, not exact timing
 *
 * 2. STRUCTURAL CHECKS
 *    - Verify synchronizer structure
 *    - Check data stability during handshake
 *    - Prove protocol phases
 *
 * 3. SPECIAL TOOLS
 *    - Cadence JasperGold CDC
 *    - Synopsys VC Formal CDC
 *    - Automated CDC verification
 *
 * What formal proves for CDC:
 *   ✓ Data stable during transfer
 *   ✓ Handshake protocol correct
 *   ✓ No combinational paths across domains
 *   ✓ Proper synchronizer structure
 *   ✓ Gray code for counters
 *   ✗ Cannot prove metastability immunity
 *
 * MTBF (Mean Time Between Failures) for metastability:
 *   MTBF = e^(Tr/τ) / (f_clk × f_data × T_0)
 *   Where:
 *     Tr = resolution time (sync chain delay)
 *     τ = metastability time constant
 *     f_clk = clock frequency
 *     f_data = data transition frequency
 *     T_0 = metastability window
 *
 * Typical MTBF with 2-FF sync at 100MHz: > 1000 years
 *
 * Best practices:
 *   1. Always use 2+ FF synchronizers
 *   2. Gray code for multi-bit counters
 *   3. Handshake for multi-bit data
 *   4. FIFO for high throughput
 *   5. Formal verification for protocol
 *   6. MTBF calculation for metastability
 */
