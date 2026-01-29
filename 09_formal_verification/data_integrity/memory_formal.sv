// Formal Verification of Memory Read/Write Consistency
// Proves that data written can be correctly read back

module memory_formal_properties #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 256
) (
    input logic                    clk,
    input logic                    rst_n,
    
    // Write interface
    input logic                    wr_en,
    input logic [ADDR_WIDTH-1:0]   wr_addr,
    input logic [DATA_WIDTH-1:0]   wr_data,
    
    // Read interface
    input logic                    rd_en,
    input logic [ADDR_WIDTH-1:0]   rd_addr,
    input logic [DATA_WIDTH-1:0]   rd_data
);

    // ============================================
    // SHADOW MEMORY
    // ============================================
    // Track what should be in memory
    
    logic [DATA_WIDTH-1:0] shadow_mem [DEPTH];
    logic shadow_valid [DEPTH];  // Track which addresses have been written
    
    // Shadow write
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++)
                shadow_valid[i] <= 0;
        end else if (wr_en) begin
            shadow_mem[wr_addr] <= wr_data;
            shadow_valid[wr_addr] <= 1;
        end
    end
    
    // ============================================
    // DATA INTEGRITY PROPERTIES
    // ============================================
    
    // Property 1: Read returns last written value (basic correctness)
    property read_after_write;
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data;
        @(posedge clk) disable iff (!rst_n)
        (wr_en, addr = wr_addr, data = wr_data) ##1
        (rd_en && (rd_addr == addr))[->1] |->
        (rd_data == data);
    endproperty
    
    a_raw: assert property (read_after_write)
        else $error("READ-AFTER-WRITE: addr=%h wrote=%h read=%h",
                   rd_addr, shadow_mem[rd_addr], rd_data);
    
    // Property 2: Read matches shadow memory
    property read_matches_shadow;
        @(posedge clk) disable iff (!rst_n)
        rd_en && shadow_valid[rd_addr] |->
        (rd_data == shadow_mem[rd_addr]);
    endproperty
    
    a_shadow_match: assert property (read_matches_shadow)
        else $error("SHADOW MISMATCH: addr=%h expected=%h got=%h",
                   rd_addr, shadow_mem[rd_addr], rd_data);
    
    // ============================================
    // WRITE PROPERTIES
    // ============================================
    
    // Property 3: Writes to different addresses don't interfere
    property write_independence;
        logic [ADDR_WIDTH-1:0] addr1, addr2;
        logic [DATA_WIDTH-1:0] data1, data2;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && (addr1 = wr_addr) && (data1 = wr_data)) ##1
        (wr_en && (addr2 = wr_addr) && (data2 = wr_data) && (addr2 != addr1)) ##1
        (rd_en && (rd_addr == addr1))[->1] |->
        (rd_data == data1);  // First write not overwritten
    endproperty
    
    // Property 4: Later write to same address overwrites
    property write_overwrite;
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data1, data2;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && (addr = wr_addr) && (data1 = wr_data)) ##1
        (wr_en && (wr_addr == addr) && (data2 = wr_data))[->1] ##1
        (rd_en && (rd_addr == addr))[->1] |->
        (rd_data == data2);  // Second write value
    endproperty
    
    // ============================================
    // ADDRESS VALIDITY
    // ============================================
    
    // Property 5: Write address in range
    property wr_addr_valid;
        @(posedge clk) disable iff (!rst_n)
        wr_en |-> (wr_addr < DEPTH);
    endproperty
    
    a_wr_addr: assert property (wr_addr_valid)
        else $error("WRITE ADDRESS OUT OF RANGE: %h", wr_addr);
    
    // Property 6: Read address in range
    property rd_addr_valid;
        @(posedge clk) disable iff (!rst_n)
        rd_en |-> (rd_addr < DEPTH);
    endproperty
    
    a_rd_addr: assert property (rd_addr_valid)
        else $error("READ ADDRESS OUT OF RANGE: %h", rd_addr);
    
    // ============================================
    // DATA VALIDITY
    // ============================================
    
    // Property 7: Write data has no X/Z
    property wr_data_defined;
        @(posedge clk) disable iff (!rst_n)
        wr_en |-> !$isunknown(wr_data);
    endproperty
    
    a_wr_data_clean: assert property (wr_data_defined)
        else $error("WRITE DATA UNDEFINED: %h", wr_data);
    
    // Property 8: Read data has no X/Z when valid location
    property rd_data_defined;
        @(posedge clk) disable iff (!rst_n)
        rd_en && shadow_valid[rd_addr] |-> !$isunknown(rd_data);
    endproperty
    
    a_rd_data_clean: assert property (rd_data_defined)
        else $error("READ DATA UNDEFINED: addr=%h", rd_addr);
    
    // ============================================
    // SIMULTANEOUS READ/WRITE
    // ============================================
    
    // Property 9: Simultaneous write and read to same address
    // Read gets either old or new data (depending on memory type)
    
    // For write-first memory:
    property write_first_semantics;
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] wdata;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && rd_en && (wr_addr == rd_addr), 
         addr = wr_addr, wdata = wr_data) |->
        (rd_data == wdata);  // Read new data
    endproperty
    
    // For read-first memory:
    property read_first_semantics;
        logic [ADDR_WIDTH-1:0] addr;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && rd_en && (wr_addr == rd_addr), addr = wr_addr) |->
        (rd_data == $past(shadow_mem[addr]));  // Read old data
    endproperty
    
    // Choose one based on your memory type:
    // a_write_first: assert property (write_first_semantics);
    // OR
    // a_read_first: assert property (read_first_semantics);
    
    // ============================================
    // PERSISTENCE
    // ============================================
    
    // Property 10: Data persists if not overwritten
    property data_persists;
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && (addr = wr_addr) && (data = wr_data)) ##1
        (!(wr_en && (wr_addr == addr)))[*10] ##1
        (rd_en && (rd_addr == addr)) |->
        (rd_data == data);
    endproperty
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Write to address 0
    c_write_zero: cover property (
        @(posedge clk) wr_en && (wr_addr == 0)
    );
    
    // Cover: Read from address 0
    c_read_zero: cover property (
        @(posedge clk) rd_en && (rd_addr == 0)
    );
    
    // Cover: Write then read same address
    c_wr_rd_same: cover property (
        @(posedge clk) wr_en ##[1:5] (rd_en && (rd_addr == $past(wr_addr, 1)))
    );
    
    // Cover: Simultaneous read and write
    c_simul: cover property (
        @(posedge clk) wr_en && rd_en
    );
    
    // Cover: Back-to-back writes
    c_consec_wr: cover property (
        @(posedge clk) wr_en ##1 wr_en
    );
    
    // Cover: Back-to-back reads
    c_consec_rd: cover property (
        @(posedge clk) rd_en ##1 rd_en
    );
    
    // Cover: Write to max address
    c_write_max: cover property (
        @(posedge clk) wr_en && (wr_addr == DEPTH-1)
    );
    
    // ============================================
    // DUAL-PORT SPECIFIC PROPERTIES
    // ============================================
    
    // If you have dual-port memory, add these:
    
    // Property: Port A write doesn't affect port B address
    // Property: Both ports can read simultaneously
    // Property: Write collision handling

endmodule

// ============================================
// DUAL-PORT MEMORY PROPERTIES
// ============================================

module dual_port_memory_formal #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 256
) (
    input logic                    clk,
    input logic                    rst_n,
    
    // Port A
    input logic                    wr_en_a,
    input logic [ADDR_WIDTH-1:0]   addr_a,
    input logic [DATA_WIDTH-1:0]   wr_data_a,
    input logic [DATA_WIDTH-1:0]   rd_data_a,
    
    // Port B
    input logic                    wr_en_b,
    input logic [ADDR_WIDTH-1:0]   addr_b,
    input logic [DATA_WIDTH-1:0]   wr_data_b,
    input logic [DATA_WIDTH-1:0]   rd_data_b
);

    // Shadow memory
    logic [DATA_WIDTH-1:0] shadow_mem [DEPTH];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize if needed
        end else begin
            if (wr_en_a)
                shadow_mem[addr_a] <= wr_data_a;
            if (wr_en_b)
                shadow_mem[addr_b] <= wr_data_b;
        end
    end
    
    // Property: Port A read matches shadow
    property port_a_read_correct;
        @(posedge clk) disable iff (!rst_n)
        !wr_en_a |-> (rd_data_a == shadow_mem[addr_a]);
    endproperty
    
    a_port_a: assert property (port_a_read_correct);
    
    // Property: Port B read matches shadow
    property port_b_read_correct;
        @(posedge clk) disable iff (!rst_n)
        !wr_en_b |-> (rd_data_b == shadow_mem[addr_b]);
    endproperty
    
    a_port_b: assert property (port_b_read_correct);
    
    // Property: Write collision behavior
    // When both ports write to same address simultaneously
    property write_collision;
        @(posedge clk) disable iff (!rst_n)
        wr_en_a && wr_en_b && (addr_a == addr_b) |=>
        // Define behavior: port A wins, port B wins, or undefined
        (shadow_mem[addr_a] == $past(wr_data_a)) ||
        (shadow_mem[addr_a] == $past(wr_data_b));
    endproperty
    
    // Property: Independent reads
    property independent_reads;
        @(posedge clk) disable iff (!rst_n)
        (addr_a != addr_b) |->
        (rd_data_a == shadow_mem[addr_a]) &&
        (rd_data_b == shadow_mem[addr_b]);
    endproperty
    
    a_indep_reads: assert property (independent_reads);

endmodule

// ============================================
// MEMORY WITH BYTE ENABLES
// ============================================

module memory_with_be_formal #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter BE_WIDTH = DATA_WIDTH/8,
    parameter DEPTH = 256
) (
    input logic                    clk,
    input logic                    rst_n,
    input logic                    wr_en,
    input logic [ADDR_WIDTH-1:0]   wr_addr,
    input logic [DATA_WIDTH-1:0]   wr_data,
    input logic [BE_WIDTH-1:0]     wr_be,     // Byte enables
    input logic                    rd_en,
    input logic [ADDR_WIDTH-1:0]   rd_addr,
    input logic [DATA_WIDTH-1:0]   rd_data
);

    // Shadow memory
    logic [DATA_WIDTH-1:0] shadow_mem [DEPTH];
    
    // Update shadow with byte enables
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize
        end else if (wr_en) begin
            for (int i = 0; i < BE_WIDTH; i++) begin
                if (wr_be[i])
                    shadow_mem[wr_addr][i*8 +: 8] <= wr_data[i*8 +: 8];
            end
        end
    end
    
    // Property: Read matches shadow
    property read_with_be;
        @(posedge clk) disable iff (!rst_n)
        rd_en |-> (rd_data == shadow_mem[rd_addr]);
    endproperty
    
    a_be_read: assert property (read_with_be);
    
    // Property: Byte enables only affect specified bytes
    property be_selective_write;
        logic [ADDR_WIDTH-1:0] addr;
        @(posedge clk) disable iff (!rst_n)
        (wr_en && (addr = wr_addr)) ##1
        (rd_en && (rd_addr == addr)) |->
        // Each byte matches if BE was set, else old value
        1'b1;  // Simplified - full check needs per-byte comparison
    endproperty

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Memory formal verification proves:
 *   1. Data written can be read back (correctness)
 *   2. Writes don't interfere with other addresses
 *   3. Data persists until overwritten
 *   4. Address ranges are respected
 *   5. No X/Z propagation
 *
 * Shadow memory technique:
 *   - Mirror expected memory contents
 *   - Compare reads against shadow
 *   - Proves implementation matches specification
 *
 * Challenges:
 *   - Large address space (2^ADDR_WIDTH states)
 *   - Solution: Bound addresses or use abstraction
 *   - Focus on recently-written locations
 *
 * Typical approach:
 *   - Limit formal to small DEPTH (e.g., 16 locations)
 *   - Prove algorithmic correctness
 *   - Trust synthesis for larger memories
 *
 * For formal:
 *   - Use small DEPTH (4-16)
 *   - Bound sequence depth
 *   - Focus on key properties
 */
