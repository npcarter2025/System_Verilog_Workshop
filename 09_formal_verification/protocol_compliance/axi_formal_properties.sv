// Formal Properties for AXI4-Lite Protocol Compliance
// AXI4-Lite is a simplified version of AXI4 for simple peripherals

module axi_lite_formal_properties #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
) (
    input logic                    aclk,
    input logic                    aresetn,
    
    // Write Address Channel
    input logic [ADDR_WIDTH-1:0]   awaddr,
    input logic [2:0]              awprot,
    input logic                    awvalid,
    input logic                    awready,
    
    // Write Data Channel
    input logic [DATA_WIDTH-1:0]   wdata,
    input logic [(DATA_WIDTH/8)-1:0] wstrb,
    input logic                    wvalid,
    input logic                    wready,
    
    // Write Response Channel
    input logic [1:0]              bresp,
    input logic                    bvalid,
    input logic                    bready,
    
    // Read Address Channel
    input logic [ADDR_WIDTH-1:0]   araddr,
    input logic [2:0]              arprot,
    input logic                    arvalid,
    input logic                    arready,
    
    // Read Data Channel
    input logic [DATA_WIDTH-1:0]   rdata,
    input logic [1:0]              rresp,
    input logic                    rvalid,
    input logic                    rready
);

    // ============================================
    // WRITE ADDRESS CHANNEL PROPERTIES
    // ============================================
    
    // Property: AWVALID once asserted, stays high until AWREADY
    property aw_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> awvalid;
    endproperty
    
    a_aw_valid: assert property (aw_valid_stable)
        else $error("AXI VIOLATION: AWVALID dropped before AWREADY");
    
    // Property: AWADDR stable while AWVALID && !AWREADY
    property aw_addr_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> $stable(awaddr);
    endproperty
    
    a_aw_addr: assert property (aw_addr_stable)
        else $error("AXI VIOLATION: AWADDR changed during AWVALID");
    
    // Property: AWPROT stable while AWVALID && !AWREADY
    property aw_prot_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> $stable(awprot);
    endproperty
    
    a_aw_prot: assert property (aw_prot_stable);
    
    // Property: No X on AWVALID
    property aw_valid_defined;
        @(posedge aclk) disable iff (!aresetn)
        !$isunknown(awvalid);
    endproperty
    
    a_aw_valid_clean: assert property (aw_valid_defined);
    
    // Property: AWADDR aligned based on data width
    property aw_addr_aligned;
        @(posedge aclk) disable iff (!aresetn)
        awvalid |-> (awaddr[1:0] == 2'b00);  // Word aligned
    endproperty
    
    a_aw_aligned: assert property (aw_addr_aligned)
        else $error("AXI VIOLATION: AWADDR not word-aligned: %h", awaddr);
    
    // ============================================
    // WRITE DATA CHANNEL PROPERTIES
    // ============================================
    
    // Property: WVALID once asserted, stays high until WREADY
    property w_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> wvalid;
    endproperty
    
    a_w_valid: assert property (w_valid_stable)
        else $error("AXI VIOLATION: WVALID dropped before WREADY");
    
    // Property: WDATA stable while WVALID && !WREADY
    property w_data_stable;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> $stable(wdata);
    endproperty
    
    a_w_data: assert property (w_data_stable)
        else $error("AXI VIOLATION: WDATA changed during WVALID");
    
    // Property: WSTRB stable while WVALID && !WREADY
    property w_strb_stable;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> $stable(wstrb);
    endproperty
    
    a_w_strb: assert property (w_strb_stable);
    
    // Property: At least one strobe bit set when writing
    property w_strb_nonzero;
        @(posedge aclk) disable iff (!aresetn)
        wvalid |-> (wstrb != '0);
    endproperty
    
    a_w_strb_set: assert property (w_strb_nonzero)
        else $error("AXI VIOLATION: WSTRB is all zeros");
    
    // ============================================
    // WRITE RESPONSE CHANNEL PROPERTIES
    // ============================================
    
    // Property: BVALID once asserted, stays high until BREADY
    property b_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        bvalid && !bready |=> bvalid;
    endproperty
    
    a_b_valid: assert property (b_valid_stable)
        else $error("AXI VIOLATION: BVALID dropped before BREADY");
    
    // Property: BRESP stable while BVALID && !BREADY
    property b_resp_stable;
        @(posedge aclk) disable iff (!aresetn)
        bvalid && !bready |=> $stable(bresp);
    endproperty
    
    a_b_resp: assert property (b_resp_stable);
    
    // Property: BRESP valid values only (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
    property b_resp_valid_values;
        @(posedge aclk) disable iff (!aresetn)
        bvalid |-> bresp inside {2'b00, 2'b01, 2'b10, 2'b11};
    endproperty
    
    a_b_resp_valid: assert property (b_resp_valid_values);
    
    // ============================================
    // WRITE TRANSACTION ORDERING
    // ============================================
    
    // Property: Write data must follow or coincide with write address
    // Track if write address has been seen
    logic aw_pending;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)
            aw_pending <= 0;
        else if (awvalid && awready)
            aw_pending <= 1;
        else if (wvalid && wready && !awvalid)
            aw_pending <= 0;
    end
    
    property w_after_aw;
        @(posedge aclk) disable iff (!aresetn)
        wvalid |-> aw_pending || awvalid;
    endproperty
    
    a_w_order: assert property (w_after_aw)
        else $error("AXI VIOLATION: WVALID before AWVALID");
    
    // Property: Response comes after both address and data
    logic aw_seen, w_seen;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            aw_seen <= 0;
            w_seen <= 0;
        end else begin
            if (awvalid && awready) aw_seen <= 1;
            if (wvalid && wready) w_seen <= 1;
            if (bvalid && bready) begin
                aw_seen <= 0;
                w_seen <= 0;
            end
        end
    end
    
    property b_after_aw_w;
        @(posedge aclk) disable iff (!aresetn)
        bvalid |-> aw_seen && w_seen;
    endproperty
    
    a_b_order: assert property (b_after_aw_w)
        else $error("AXI VIOLATION: BVALID before AW/W complete");
    
    // ============================================
    // READ ADDRESS CHANNEL PROPERTIES
    // ============================================
    
    // Property: ARVALID once asserted, stays high until ARREADY
    property ar_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> arvalid;
    endproperty
    
    a_ar_valid: assert property (ar_valid_stable)
        else $error("AXI VIOLATION: ARVALID dropped before ARREADY");
    
    // Property: ARADDR stable while ARVALID && !ARREADY
    property ar_addr_stable;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> $stable(araddr);
    endproperty
    
    a_ar_addr: assert property (ar_addr_stable)
        else $error("AXI VIOLATION: ARADDR changed during ARVALID");
    
    // Property: ARADDR aligned
    property ar_addr_aligned;
        @(posedge aclk) disable iff (!aresetn)
        arvalid |-> (araddr[1:0] == 2'b00);
    endproperty
    
    a_ar_aligned: assert property (ar_addr_aligned);
    
    // ============================================
    // READ DATA CHANNEL PROPERTIES
    // ============================================
    
    // Property: RVALID once asserted, stays high until RREADY
    property r_valid_stable;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> rvalid;
    endproperty
    
    a_r_valid: assert property (r_valid_stable)
        else $error("AXI VIOLATION: RVALID dropped before RREADY");
    
    // Property: RDATA stable while RVALID && !RREADY
    property r_data_stable;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> $stable(rdata);
    endproperty
    
    a_r_data: assert property (r_data_stable);
    
    // Property: RRESP stable while RVALID && !RREADY
    property r_resp_stable;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> $stable(rresp);
    endproperty
    
    a_r_resp: assert property (r_resp_stable);
    
    // Property: RRESP valid values
    property r_resp_valid_values;
        @(posedge aclk) disable iff (!aresetn)
        rvalid |-> rresp inside {2'b00, 2'b01, 2'b10, 2'b11};
    endproperty
    
    a_r_resp_valid: assert property (r_resp_valid_values);
    
    // ============================================
    // READ TRANSACTION ORDERING
    // ============================================
    
    // Property: Read data comes after read address
    logic ar_pending_read;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)
            ar_pending_read <= 0;
        else if (arvalid && arready)
            ar_pending_read <= 1;
        else if (rvalid && rready && !arvalid)
            ar_pending_read <= 0;
    end
    
    property r_after_ar;
        @(posedge aclk) disable iff (!aresetn)
        rvalid |-> ar_pending_read || arvalid;
    endproperty
    
    a_r_order: assert property (r_after_ar)
        else $error("AXI VIOLATION: RVALID before ARVALID");
    
    // ============================================
    // RESET BEHAVIOR
    // ============================================
    
    // Property: All valid signals deasserted after reset
    property reset_valids_clear;
        @(posedge aclk)
        !aresetn |=> !awvalid && !wvalid && !bvalid && !arvalid && !rvalid;
    endproperty
    
    a_reset: assert property (reset_valids_clear)
        else $error("AXI VIOLATION: Valid signals not cleared after reset");
    
    // ============================================
    // DEADLOCK PREVENTION
    // ============================================
    
    // Property: READY signals eventually assert (no permanent stall)
    property aw_no_deadlock;
        @(posedge aclk) disable iff (!aresetn)
        awvalid |-> ##[1:100] awready;
    endproperty
    
    a_aw_deadlock: assert property (aw_no_deadlock)
        else $error("DEADLOCK: AWREADY not asserted within 100 cycles");
    
    property w_no_deadlock;
        @(posedge aclk) disable iff (!aresetn)
        wvalid |-> ##[1:100] wready;
    endproperty
    
    a_w_deadlock: assert property (w_no_deadlock);
    
    property ar_no_deadlock;
        @(posedge aclk) disable iff (!aresetn)
        arvalid |-> ##[1:100] arready;
    endproperty
    
    a_ar_deadlock: assert property (ar_no_deadlock);
    
    // ============================================
    // COVERAGE PROPERTIES
    // ============================================
    
    // Cover: Successful write transaction
    sequence write_transaction;
        (awvalid && awready) ##[0:5] (wvalid && wready) ##[1:10] (bvalid && bready);
    endsequence
    
    c_write_trans: cover property (@(posedge aclk) write_transaction);
    
    // Cover: Successful read transaction
    sequence read_transaction;
        (arvalid && arready) ##[1:10] (rvalid && rready);
    endsequence
    
    c_read_trans: cover property (@(posedge aclk) read_transaction);
    
    // Cover: Simultaneous write and read address
    c_simul_aw_ar: cover property (
        @(posedge aclk) awvalid && arvalid
    );
    
    // Cover: Back-to-back writes
    c_back_to_back_write: cover property (
        @(posedge aclk) (bvalid && bready) ##1 (awvalid && awready)
    );
    
    // Cover: All response types
    c_okay_resp: cover property (@(posedge aclk) bvalid && (bresp == 2'b00));
    c_slverr: cover property (@(posedge aclk) bvalid && (bresp == 2'b10));
    c_decerr: cover property (@(posedge aclk) bvalid && (bresp == 2'b11));
    
    // Cover: All strobe patterns
    c_full_strb: cover property (@(posedge aclk) wvalid && (wstrb == '1));
    c_byte_strb: cover property (@(posedge aclk) wvalid && (wstrb == 4'b0001));
    c_half_strb: cover property (@(posedge aclk) wvalid && (wstrb == 4'b0011));

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * These properties verify AXI4-Lite protocol compliance.
 * 
 * To use:
 * 1. Bind this module to your AXI master or slave
 * 2. Run formal verification tool
 * 3. All assertions should prove
 * 4. All covers should be reachable
 *
 * Common violations:
 * - Dropping valid before ready (most common bug!)
 * - Changing address/data while waiting
 * - Wrong transaction ordering
 * - Misaligned addresses
 * - Incorrect response codes
 *
 * The formal tool will provide counterexamples showing
 * exact sequences that violate the protocol.
 */
