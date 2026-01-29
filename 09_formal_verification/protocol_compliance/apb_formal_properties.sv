// Formal Properties for APB (Advanced Peripheral Bus) Protocol
// APB is a simple, low-power bus protocol for peripheral devices

module apb_formal_properties #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
) (
    input logic                    pclk,
    input logic                    presetn,
    
    // APB signals
    input logic [ADDR_WIDTH-1:0]   paddr,
    input logic                    psel,      // Select
    input logic                    penable,   // Enable (2nd cycle of transfer)
    input logic                    pwrite,    // 1=Write, 0=Read
    input logic [DATA_WIDTH-1:0]   pwdata,    // Write data
    input logic [(DATA_WIDTH/8)-1:0] pstrb,   // Write strobes
    input logic                    pready,    // Slave ready
    input logic [DATA_WIDTH-1:0]   prdata,    // Read data
    input logic                    pslverr    // Slave error
);

    // ============================================
    // APB PROTOCOL STATES
    // ============================================
    // APB has 3 states:
    // - IDLE: No transfer
    // - SETUP: psel=1, penable=0 (address phase)
    // - ACCESS: psel=1, penable=1 (data phase)
    
    typedef enum logic [1:0] {
        IDLE   = 2'b00,
        SETUP  = 2'b01,
        ACCESS = 2'b10
    } apb_state_t;
    
    // Track current state
    apb_state_t state;
    
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            state <= IDLE;
        else begin
            case (state)
                IDLE:   if (psel && !penable) state <= SETUP;
                SETUP:  if (penable) state <= ACCESS;
                ACCESS: if (pready) state <= psel ? SETUP : IDLE;
            endcase
        end
    end
    
    // ============================================
    // BASIC PROTOCOL RULES
    // ============================================
    
    // Rule 1: PENABLE must be low when PSEL first asserts
    property setup_phase;
        @(posedge pclk) disable iff (!presetn)
        $rose(psel) |-> !penable;
    endproperty
    
    a_setup: assert property (setup_phase)
        else $error("APB VIOLATION: PENABLE high when PSEL first asserts");
    
    // Rule 2: PENABLE follows PSEL after one cycle
    property enable_after_select;
        @(posedge pclk) disable iff (!presetn)
        (psel && !penable) |=> penable;
    endproperty
    
    a_enable_timing: assert property (enable_after_select)
        else $error("APB VIOLATION: PENABLE not asserted after PSEL");
    
    // Rule 3: Transfer completes when PSEL && PENABLE && PREADY
    // This is more of a definition
    
    // Rule 4: PSEL and PENABLE must remain stable during wait states
    property sel_stable_during_wait;
        @(posedge pclk) disable iff (!presetn)
        psel && penable && !pready |=> psel && penable;
    endproperty
    
    a_sel_stable: assert property (sel_stable_during_wait)
        else $error("APB VIOLATION: PSEL/PENABLE changed during wait");
    
    // ============================================
    // ADDRESS AND CONTROL STABILITY
    // ============================================
    
    // Rule 5: PADDR stable during transfer
    property addr_stable;
        @(posedge pclk) disable iff (!presetn)
        psel && !pready |=> $stable(paddr);
    endproperty
    
    a_addr_stable: assert property (addr_stable)
        else $error("APB VIOLATION: PADDR changed during transfer");
    
    // Rule 6: PWRITE stable during transfer
    property write_stable;
        @(posedge pclk) disable iff (!presetn)
        psel && !pready |=> $stable(pwrite);
    endproperty
    
    a_write_stable: assert property (write_stable)
        else $error("APB VIOLATION: PWRITE changed during transfer");
    
    // ============================================
    // WRITE DATA RULES
    // ============================================
    
    // Rule 7: PWDATA stable during write transfer
    property wdata_stable;
        @(posedge pclk) disable iff (!presetn)
        psel && pwrite && !pready |=> $stable(pwdata);
    endproperty
    
    a_wdata_stable: assert property (wdata_stable)
        else $error("APB VIOLATION: PWDATA changed during write");
    
    // Rule 8: PSTRB stable during write transfer
    property strb_stable;
        @(posedge pclk) disable iff (!presetn)
        psel && pwrite && !pready |=> $stable(pstrb);
    endproperty
    
    a_strb_stable: assert property (strb_stable);
    
    // Rule 9: PSTRB only valid during writes
    property strb_write_only;
        @(posedge pclk) disable iff (!presetn)
        psel && !pwrite |-> (pstrb == '0);
    endproperty
    
    // Note: Some implementations allow don't-care on reads
    // a_strb_write: assert property (strb_write_only);
    
    // ============================================
    // READ DATA RULES
    // ============================================
    
    // Rule 10: PRDATA valid when PREADY during read
    property rdata_valid_on_ready;
        @(posedge pclk) disable iff (!presetn)
        psel && penable && !pwrite && pready |-> !$isunknown(prdata);
    endproperty
    
    a_rdata_valid: assert property (rdata_valid_on_ready)
        else $error("APB VIOLATION: PRDATA contains X during read completion");
    
    // ============================================
    // ERROR RESPONSE
    // ============================================
    
    // Rule 11: PSLVERR stable during transfer
    property slverr_stable;
        @(posedge pclk) disable iff (!presetn)
        psel && penable && !pready |=> $stable(pslverr);
    endproperty
    
    a_slverr_stable: assert property (slverr_stable);
    
    // Rule 12: PSLVERR only valid during ACCESS phase
    property slverr_access_only;
        @(posedge pclk) disable iff (!presetn)
        pslverr |-> (psel && penable);
    endproperty
    
    a_slverr_timing: assert property (slverr_access_only)
        else $error("APB VIOLATION: PSLVERR asserted outside ACCESS phase");
    
    // ============================================
    // STATE MACHINE CHECKS
    // ============================================
    
    // Rule 13: Valid state transitions only
    property valid_state_transitions;
        @(posedge pclk) disable iff (!presetn)
        (state == IDLE)   |=> (state inside {IDLE, SETUP}) ##0
        (state == SETUP)  |=> (state == ACCESS) ##0
        (state == ACCESS) |=> (state inside {IDLE, SETUP, ACCESS});
    endproperty
    
    a_state_trans: assert property (valid_state_transitions)
        else $error("APB STATE ERROR: Invalid transition from %s", state.name());
    
    // ============================================
    // TIMING CHECKS
    // ============================================
    
    // Rule 14: Minimum transfer is 2 cycles (SETUP + ACCESS)
    property min_transfer_time;
        @(posedge pclk) disable iff (!presetn)
        $rose(psel) |-> ##2 (pready || !psel);
    endproperty
    
    a_min_time: assert property (min_transfer_time)
        else $error("APB VIOLATION: Transfer too short");
    
    // Rule 15: PREADY eventually asserts (no permanent wait)
    property ready_eventually;
        @(posedge pclk) disable iff (!presetn)
        psel && penable |-> ##[0:100] pready;
    endproperty
    
    a_no_deadlock: assert property (ready_eventually)
        else $error("APB DEADLOCK: PREADY not asserted within 100 cycles");
    
    // ============================================
    // RESET BEHAVIOR
    // ============================================
    
    // Rule 16: All signals deasserted after reset
    property reset_state;
        @(posedge pclk)
        !presetn |=> !psel && !penable;
    endproperty
    
    a_reset: assert property (reset_state)
        else $error("APB VIOLATION: Signals not cleared after reset");
    
    // ============================================
    // SIGNAL DEFINITIONS
    // ============================================
    
    // Rule 17: No X/Z on control signals
    property control_defined;
        @(posedge pclk) disable iff (!presetn)
        !$isunknown({psel, penable, pwrite, pready});
    endproperty
    
    a_control_clean: assert property (control_defined)
        else $error("APB VIOLATION: X/Z on control signals");
    
    // Rule 18: Address aligned for data width
    property addr_aligned;
        @(posedge pclk) disable iff (!presetn)
        psel |-> (paddr[1:0] == 2'b00);  // Word aligned
    endproperty
    
    a_addr_aligned: assert property (addr_aligned)
        else $error("APB VIOLATION: Misaligned address %h", paddr);
    
    // ============================================
    // COVERAGE PROPERTIES
    // ============================================
    
    // Cover: Successful write
    sequence write_transfer;
        (psel && !penable && pwrite) ##1 
        (psel && penable && pready);
    endsequence
    
    c_write: cover property (@(posedge pclk) write_transfer);
    
    // Cover: Successful read
    sequence read_transfer;
        (psel && !penable && !pwrite) ##1 
        (psel && penable && pready);
    endsequence
    
    c_read: cover property (@(posedge pclk) read_transfer);
    
    // Cover: Write with wait states
    sequence write_with_wait;
        (psel && !penable && pwrite) ##1
        (psel && penable && !pready)[*1:5] ##1
        (psel && penable && pready);
    endsequence
    
    c_write_wait: cover property (@(posedge pclk) write_with_wait);
    
    // Cover: Back-to-back transfers
    c_back_to_back: cover property (
        @(posedge pclk) (psel && penable && pready) ##1 (psel && !penable)
    );
    
    // Cover: Error response
    c_error: cover property (
        @(posedge pclk) psel && penable && pslverr
    );
    
    // Cover: All byte strobes
    c_strb_full: cover property (@(posedge pclk) psel && (pstrb == '1));
    c_strb_byte0: cover property (@(posedge pclk) psel && (pstrb == 4'b0001));
    c_strb_byte1: cover property (@(posedge pclk) psel && (pstrb == 4'b0010));
    c_strb_half: cover property (@(posedge pclk) psel && (pstrb == 4'b0011));
    
    // ============================================
    // INTEGRATION CHECKS
    // ============================================
    
    // Rule 19: Transfer count tracking
    logic [31:0] transfer_count;
    
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            transfer_count <= 0;
        else if (psel && penable && pready)
            transfer_count <= transfer_count + 1;
    end
    
    // Property: Transfers only complete in ACCESS phase
    property transfer_in_access;
        @(posedge pclk) disable iff (!presetn)
        (psel && penable && pready) |-> (state == ACCESS);
    endproperty
    
    a_trans_access: assert property (transfer_in_access);

endmodule

// ============================================
// USAGE EXAMPLE
// ============================================

/*
 * Bind to APB master:
 *   bind apb_master apb_formal_properties checker (.*);
 *
 * Bind to APB slave:
 *   bind apb_slave apb_formal_properties checker (.*);
 *
 * APB Protocol Summary:
 *   - Simple 2-cycle protocol (SETUP + ACCESS)
 *   - PREADY extends ACCESS phase (wait states)
 *   - Multiplexed address/data bus
 *   - No pipelining (one transfer at a time)
 *   - Low gate count, low power
 *
 * Common Violations:
 *   - PENABLE high during SETUP
 *   - Changing address during transfer
 *   - Missing PREADY assertion
 *   - Invalid state transitions
 */
