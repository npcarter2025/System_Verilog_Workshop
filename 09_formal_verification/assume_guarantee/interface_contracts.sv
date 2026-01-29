// Interface Contracts using Assume-Guarantee Reasoning
// Defines contracts between modules for compositional verification

module interface_contract_example (
    input logic        clk,
    input logic        rst_n,
    
    // Producer interface
    input logic        prod_valid,
    input logic        prod_ready,
    input logic [31:0] prod_data,
    
    // Consumer interface  
    input logic        cons_valid,
    input logic        cons_ready,
    input logic [31:0] cons_data
);

    // ============================================
    // PRODUCER CONTRACT
    // ============================================
    
    // ASSUMES (what producer expects from environment):
    
    // Assumption: Ready eventually asserts
    property producer_assume_ready;
        @(posedge clk) disable iff (!rst_n)
        prod_valid |-> ##[1:10] prod_ready;
    endproperty
    
    assume_prod_ready: assume property (producer_assume_ready);
    
    // GUARANTEES (what producer promises):
    
    // Guarantee: Valid stable until ready
    property producer_guarantee_stable;
        @(posedge clk) disable iff (!rst_n)
        prod_valid && !prod_ready |=> prod_valid;
    endproperty
    
    assert_prod_stable: assert property (producer_guarantee_stable);
    
    // Guarantee: Data stable until transfer
    property producer_guarantee_data;
        @(posedge clk) disable iff (!rst_n)
        prod_valid && !prod_ready |=> $stable(prod_data);
    endproperty
    
    assert_prod_data: assert property (producer_guarantee_data);
    
    // ============================================
    // CONSUMER CONTRACT
    // ============================================
    
    // ASSUMES (what consumer expects):
    
    // Assumption: Valid follows protocol
    property consumer_assume_valid;
        @(posedge clk) disable iff (!rst_n)
        cons_valid && !cons_ready |=> cons_valid;
    endproperty
    
    assume_cons_valid: assume property (consumer_assume_valid);
    
    // Assumption: Data stable
    property consumer_assume_data;
        @(posedge clk) disable iff (!rst_n)
        cons_valid && !cons_ready |=> $stable(cons_data);
    endproperty
    
    assume_cons_data: assume property (consumer_assume_data);
    
    // GUARANTEES (what consumer promises):
    
    // Guarantee: Ready eventually asserts
    property consumer_guarantee_ready;
        @(posedge clk) disable iff (!rst_n)
        cons_valid |-> ##[1:10] cons_ready;
    endproperty
    
    assert_cons_ready: assert property (consumer_guarantee_ready);

endmodule

// ============================================
// MASTER-SLAVE CONTRACT
// ============================================

module master_slave_contract (
    input logic        clk,
    input logic        rst_n,
    
    // Master outputs / Slave inputs
    input logic        m_req,
    input logic [31:0] m_addr,
    input logic [31:0] m_wdata,
    input logic        m_wr_en,
    
    // Slave outputs / Master inputs
    input logic        s_ack,
    input logic [31:0] s_rdata,
    input logic        s_error
);

    // ============================================
    // MASTER CONTRACT
    // ============================================
    
    // ASSUMES:
    assume_ack_timing: assume property (
        @(posedge clk) disable iff (!rst_n)
        m_req |-> ##[1:20] s_ack
    );
    
    assume_no_spurious_ack: assume property (
        @(posedge clk) disable iff (!rst_n)
        s_ack |-> m_req
    );
    
    // GUARANTEES:
    assert_req_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_req && !s_ack |=> m_req
    );
    
    assert_addr_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_req && !s_ack |=> $stable(m_addr)
    );
    
    assert_addr_aligned: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_req |-> (m_addr[1:0] == 2'b00)
    );
    
    // ============================================
    // SLAVE CONTRACT
    // ============================================
    
    // ASSUMES:
    assume_req_protocol: assume property (
        @(posedge clk) disable iff (!rst_n)
        m_req && !s_ack |=> m_req
    );
    
    assume_addr_stable_slave: assume property (
        @(posedge clk) disable iff (!rst_n)
        m_req && !s_ack |=> $stable(m_addr)
    );
    
    // GUARANTEES:
    assert_ack_timing: assert property (
        @(posedge clk) disable iff (!rst_n)
        m_req |-> ##[1:20] s_ack
    );
    
    assert_rdata_valid: assert property (
        @(posedge clk) disable iff (!rst_n)
        s_ack && !m_wr_en |-> !$isunknown(s_rdata)
    );

endmodule

// ============================================
// LAYERED PROTOCOL CONTRACT
// ============================================

module layered_protocol_contract (
    input logic clk,
    input logic rst_n,
    
    // Physical layer
    input logic phy_tx_en,
    input logic phy_tx_ready,
    
    // Link layer
    input logic link_packet_valid,
    input logic link_packet_ready,
    
    // Network layer
    input logic net_msg_valid,
    input logic net_msg_ready
);

    // ============================================
    // LAYER 1 (Physical) CONTRACT
    // ============================================
    
    // ASSUMES: Link layer provides data
    assume_link_provides: assume property (
        @(posedge clk) disable iff (!rst_n)
        phy_tx_ready |-> ##[0:5] link_packet_valid
    );
    
    // GUARANTEES: Can transmit when ready
    assert_phy_ready: assert property (
        @(posedge clk) disable iff (!rst_n)
        link_packet_valid |-> ##[1:10] phy_tx_ready
    );
    
    // ============================================
    // LAYER 2 (Link) CONTRACT
    // ============================================
    
    // ASSUMES: Physical layer ready, Network layer provides
    assume_phy_accepts: assume property (
        @(posedge clk) disable iff (!rst_n)
        phy_tx_en |-> ##[1:5] phy_tx_ready
    );
    
    assume_net_provides: assume property (
        @(posedge clk) disable iff (!rst_n)
        link_packet_ready |-> ##[0:5] net_msg_valid
    );
    
    // GUARANTEES: Packets delivered
    assert_link_delivery: assert property (
        @(posedge clk) disable iff (!rst_n)
        link_packet_valid && link_packet_ready |-> 
        ##[1:10] phy_tx_en
    );
    
    // ============================================
    // LAYER 3 (Network) CONTRACT
    // ============================================
    
    // ASSUMES: Link layer accepts
    assume_link_accepts: assume property (
        @(posedge clk) disable iff (!rst_n)
        net_msg_valid |-> ##[1:20] link_packet_ready
    );
    
    // GUARANTEES: Message formation
    assert_msg_valid: assert property (
        @(posedge clk) disable iff (!rst_n)
        net_msg_valid |-> !$isunknown(net_msg_ready)
    );

endmodule

// ============================================
// MODULAR VERIFICATION CONTRACT
// ============================================

module module_interface_contract #(
    parameter DATA_WIDTH = 32
) (
    input logic                   clk,
    input logic                   rst_n,
    input logic                   in_valid,
    input logic                   in_ready,
    input logic [DATA_WIDTH-1:0]  in_data,
    input logic                   out_valid,
    input logic                   out_ready,
    input logic [DATA_WIDTH-1:0]  out_data
);

    // ============================================
    // INPUT INTERFACE CONTRACT
    // ============================================
    
    // ASSUMES about input:
    assume_in_protocol: assume property (
        @(posedge clk) disable iff (!rst_n)
        in_valid && !in_ready |=> in_valid
    );
    
    assume_in_data_stable: assume property (
        @(posedge clk) disable iff (!rst_n)
        in_valid && !in_ready |=> $stable(in_data)
    );
    
    // ============================================
    // OUTPUT INTERFACE CONTRACT
    // ============================================
    
    // GUARANTEES about output:
    assert_out_protocol: assert property (
        @(posedge clk) disable iff (!rst_n)
        out_valid && !out_ready |=> out_valid
    );
    
    assert_out_data_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        out_valid && !out_ready |=> $stable(out_data)
    );
    
    // ============================================
    // FUNCTIONAL CONTRACT
    // ============================================
    
    // GUARANTEES: Output eventually produced from input
    assert_responsiveness: assert property (
        @(posedge clk) disable iff (!rst_n)
        (in_valid && in_ready) |-> ##[1:10] out_valid
    );
    
    // GUARANTEES: Data transformation is correct
    // (This depends on what module does)
    // Example: If module increments:
    property data_transform;
        logic [DATA_WIDTH-1:0] saved_in;
        @(posedge clk) disable iff (!rst_n)
        (in_valid && in_ready, saved_in = in_data) |->
        ##[1:10] (out_valid && (out_data == saved_in + 1));
    endproperty
    
    // assert_transform: assert property (data_transform);

endmodule

// ============================================
// HIERARCHICAL VERIFICATION CONTRACT
// ============================================

module hierarchical_contract (
    input logic clk,
    input logic rst_n,
    
    // Top-level interface
    input logic top_req,
    input logic top_ack,
    
    // Internal module A interface
    input logic mod_a_req,
    input logic mod_a_ack,
    
    // Internal module B interface
    input logic mod_b_req,
    input logic mod_b_ack
);

    // ============================================
    // TOP-LEVEL CONTRACT
    // ============================================
    
    // Assumes at top level
    assume_top_req: assume property (
        @(posedge clk) disable iff (!rst_n)
        top_req |-> ##[1:50] top_ack
    );
    
    // Guarantees at top level
    assert_top_response: assert property (
        @(posedge clk) disable iff (!rst_n)
        top_req |-> ##[1:100] top_ack
    );
    
    // ============================================
    // MODULE A CONTRACT (Leaf Module)
    // ============================================
    
    // Module A assumes its input behaves
    assume_mod_a_in: assume property (
        @(posedge clk) disable iff (!rst_n)
        mod_a_req |-> ##[1:20] mod_a_ack
    );
    
    // Module A guarantees its output
    assert_mod_a_out: assert property (
        @(posedge clk) disable iff (!rst_n)
        mod_a_req |-> ##[1:10] mod_a_ack
    );
    
    // ============================================
    // COMPOSITIONAL REASONING
    // ============================================
    
    // If Module A guarantees fast response (1-10 cycles)
    // And Module B guarantees fast response (1-10 cycles)
    // Then Top guarantees combined response (1-20 cycles)
    
    // This allows verifying modules independently!

endmodule

// ============================================
// CONTRACT TEMPLATES
// ============================================

/*
 * Standard Contract Template:
 *
 * module my_module_contract;
 *     // ASSUMES: What this module expects from environment
 *     assume property (input_protocol);
 *     assume property (input_timing);
 *     assume property (input_values);
 *
 *     // GUARANTEES: What this module promises
 *     assert property (output_protocol);
 *     assert property (output_timing);
 *     assert property (functional_correctness);
 *
 *     // COVERS: Verify assumptions are reasonable
 *     cover property (input_scenarios);
 *     cover property (output_scenarios);
 * endmodule
 *
 * Benefits:
 *   - Modular verification (one module at a time)
 *   - Reusable contracts
 *   - Clear interface specifications
 *   - Compositional reasoning
 *   - Parallel verification
 *
 * Integration:
 *   - Verify producer's guarantees match consumer's assumptions
 *   - Chain contracts: A→B→C
 *   - Prove system-level properties from module contracts
 */
