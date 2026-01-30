// ============================================================================
// protocol_constraints.sv - Protocol-Specific Constraint Patterns
// ============================================================================

module protocol_constraints;
    
    // ========================================================================
    // AXI4 Protocol Constraints
    // ========================================================================
    
    class axi_transaction;
        rand bit [31:0] addr;
        rand bit [7:0] len;      // AWLEN/ARLEN (0-255 beats)
        rand bit [2:0] size;     // AWSIZE/ARSIZE (1, 2, 4, 8 bytes)
        rand bit [1:0] burst;    // AWBURST/ARBURST (FIXED, INCR, WRAP)
        
        typedef enum bit [1:0] {
            FIXED = 2'b00,
            INCR  = 2'b01,
            WRAP  = 2'b10
        } burst_e;
        
        // AXI size encoding
        constraint size_c {
            size inside {[0:3]};  // 1B, 2B, 4B, 8B
        }
        
        // AXI length (beats - 1)
        constraint len_c {
            len inside {[0:255]};
        }
        
        // Burst type
        constraint burst_c {
            burst inside {FIXED, INCR, WRAP};
        }
        
        // Address alignment to size
        constraint addr_align_c {
            (size == 0) -> (addr[0:0] == 1'b0);
            (size == 1) -> (addr[1:0] == 2'b00);
            (size == 2) -> (addr[2:0] == 3'b000);
            (size == 3) -> (addr[3:0] == 4'h0);
        }
        
        // WRAP burst specific rules
        constraint wrap_rules_c {
            (burst == WRAP) -> {
                // Length must be 2, 4, 8, or 16
                len inside {1, 3, 7, 15};
                
                // Address aligned to total size
                (len == 1)  -> (addr[((size + 1) - 1):0] == 0);  // 2 beats
                (len == 3)  -> (addr[((size + 2) - 1):0] == 0);  // 4 beats
                (len == 7)  -> (addr[((size + 3) - 1):0] == 0);  // 8 beats
                (len == 15) -> (addr[((size + 4) - 1):0] == 0);  // 16 beats
            }
        }
        
        // No 4KB boundary crossing for narrow transfers
        constraint boundary_c {
            (size < 3) -> {
                ((addr[11:0] + ((len + 1) * (1 << size))) <= 12'h1000);
            }
        }
    endclass
    
    // ========================================================================
    // APB Protocol Constraints
    // ========================================================================
    
    class apb_transaction;
        rand bit [31:0] paddr;
        rand bit [31:0] pwdata;
        rand bit        pwrite;
        rand bit [2:0]  pprot;    // Protection
        rand bit [3:0]  pstrb;    // Byte strobes
        
        // Address must be word-aligned
        constraint addr_align_c {
            paddr[1:0] == 2'b00;
        }
        
        // Valid strobe patterns
        constraint strb_c {
            pwrite -> (pstrb != 4'b0000);  // At least one byte
            
            // Common patterns
            pstrb inside {
                4'b0001,  // Byte 0
                4'b0010,  // Byte 1
                4'b0100,  // Byte 2
                4'b1000,  // Byte 3
                4'b0011,  // Half-word low
                4'b1100,  // Half-word high
                4'b1111   // Full word
            };
        }
        
        // Data alignment with strobe
        constraint data_strb_c {
            pwrite -> {
                (!pstrb[0]) -> (pwdata[7:0] == 8'h0);
                (!pstrb[1]) -> (pwdata[15:8] == 8'h0);
                (!pstrb[2]) -> (pwdata[23:16] == 8'h0);
                (!pstrb[3]) -> (pwdata[31:24] == 8'h0);
            }
        }
    endclass
    
    // ========================================================================
    // AHB Protocol Constraints
    // ========================================================================
    
    class ahb_transaction;
        rand bit [31:0] haddr;
        rand bit [2:0]  hburst;   // Burst type
        rand bit [2:0]  hsize;    // Transfer size
        rand bit [1:0]  htrans;   // Transfer type
        rand bit        hwrite;
        
        typedef enum bit [2:0] {
            SINGLE = 3'b000,
            INCR   = 3'b001,
            WRAP4  = 3'b010,
            INCR4  = 3'b011,
            WRAP8  = 3'b100,
            INCR8  = 3'b101,
            WRAP16 = 3'b110,
            INCR16 = 3'b111
        } burst_e;
        
        typedef enum bit [1:0] {
            IDLE   = 2'b00,
            BUSY   = 2'b01,
            NONSEQ = 2'b10,
            SEQ    = 2'b11
        } trans_e;
        
        constraint size_c {
            hsize inside {[0:2]};  // Byte, half-word, word
        }
        
        constraint trans_c {
            htrans inside {IDLE, NONSEQ, SEQ};  // BUSY is special
        }
        
        constraint burst_c {
            hburst inside {SINGLE, INCR, WRAP4, INCR4, WRAP8, INCR8, WRAP16, INCR16};
        }
        
        // Address alignment
        constraint addr_align_c {
            (hsize == 0) -> (haddr[0:0] == 1'b0);
            (hsize == 1) -> (haddr[1:0] == 2'b00);
            (hsize == 2) -> (haddr[2:0] == 3'b000);
        }
        
        // WRAP burst alignment
        constraint wrap_align_c {
            (hburst == WRAP4)  -> (haddr[(hsize + 2 - 1):0] == 0);
            (hburst == WRAP8)  -> (haddr[(hsize + 3 - 1):0] == 0);
            (hburst == WRAP16) -> (haddr[(hsize + 4 - 1):0] == 0);
        }
        
        // 1KB boundary rule
        constraint boundary_c {
            ((haddr[9:0] + (1 << hsize)) <= 10'h400);
        }
    endclass
    
    // ========================================================================
    // PCIe TLP Constraints
    // ========================================================================
    
    class pcie_tlp;
        rand bit [1:0]  fmt;      // Format
        rand bit [4:0]  tlp_type;
        rand bit [9:0]  length;   // DWords
        rand bit [63:0] addr;
        rand bit [6:0]  lower_addr; // For alignment
        rand bit [3:0]  first_be;
        rand bit [3:0]  last_be;
        
        // Length in DWords (1-1024)
        constraint length_c {
            length inside {[1:1024]};
        }
        
        // Address alignment
        constraint addr_align_c {
            addr[1:0] == 2'b00;  // DWord aligned
        }
        
        // Byte enables consistency
        constraint be_c {
            // First BE must be contiguous
            first_be inside {4'b0001, 4'b0011, 4'b0111, 4'b1111,
                            4'b0010, 4'b0100, 4'b1000,
                            4'b0110, 4'b1100, 4'b1110};
            
            // Single DWord: last_be must be 0
            (length == 1) -> (last_be == 4'b0000);
            
            // Multiple DWords: last_be must be contiguous
            (length > 1) -> {
                last_be inside {4'b0001, 4'b0011, 4'b0111, 4'b1111,
                               4'b0010, 4'b0100, 4'b1000,
                               4'b0110, 4'b1100, 4'b1110};
            }
        }
        
        // Lower address matches first_be
        constraint lower_addr_c {
            (first_be == 4'b0001) -> (lower_addr[1:0] == 2'b00);
            (first_be == 4'b0010) -> (lower_addr[1:0] == 2'b01);
            (first_be == 4'b0100) -> (lower_addr[1:0] == 2'b10);
            (first_be == 4'b1000) -> (lower_addr[1:0] == 2'b11);
        }
    endclass
    
    // ========================================================================
    // Ethernet Frame Constraints
    // ========================================================================
    
    class ethernet_frame;
        rand bit [47:0] dest_mac;
        rand bit [47:0] src_mac;
        rand bit [15:0] ethertype;
        rand bit [7:0]  payload[];
        rand bit [31:0] fcs;  // Frame Check Sequence
        
        // Valid frame size (64-1518 bytes total)
        // Header (14) + Payload (46-1500) + FCS (4)
        constraint payload_size_c {
            payload.size() inside {[46:1500]};
        }
        
        // Common ethertypes
        constraint ethertype_c {
            ethertype dist {
                16'h0800 := 70,  // IPv4
                16'h86DD := 20,  // IPv6
                16'h0806 := 5,   // ARP
                16'h8100 := 5    // VLAN
            };
        }
        
        // Multicast/unicast
        constraint mac_c {
            // Unicast: LSB of first byte = 0
            dest_mac[0] dist {1'b0 := 90, 1'b1 := 10};
        }
        
        function void post_randomize();
            // Calculate FCS (simplified - real CRC32)
            fcs = dest_mac[31:0] ^ src_mac[31:0] ^ ethertype;
        endfunction
    endclass
    
    initial begin
        axi_transaction axi;
        apb_transaction apb;
        ahb_transaction ahb;
        pcie_tlp pcie;
        ethernet_frame eth;
        
        $display("=== Protocol Constraint Patterns ===\n");
        
        // AXI
        $display("--- AXI4 ---");
        axi = new();
        repeat(5) begin
            assert(axi.randomize());
            $display("addr=0x%0h, len=%0d, size=%0dB, burst=%0d",
                    axi.addr, axi.len + 1, (1 << axi.size), axi.burst);
        end
        
        // APB
        $display("\n--- APB ---");
        apb = new();
        repeat(5) begin
            assert(apb.randomize());
            $display("%s addr=0x%0h, data=0x%0h, strb=%04b",
                    apb.pwrite ? "WRITE" : "READ",
                    apb.paddr, apb.pwdata, apb.pstrb);
        end
        
        // AHB
        $display("\n--- AHB ---");
        ahb = new();
        repeat(5) begin
            assert(ahb.randomize());
            $display("addr=0x%0h, size=%0d, burst=%0d, trans=%0d",
                    ahb.haddr, ahb.hsize, ahb.hburst, ahb.htrans);
        end
        
        // PCIe
        $display("\n--- PCIe TLP ---");
        pcie = new();
        repeat(3) begin
            assert(pcie.randomize());
            $display("addr=0x%0h, len=%0d DWords, first_be=%04b, last_be=%04b",
                    pcie.addr, pcie.length, pcie.first_be, pcie.last_be);
        end
        
        // Ethernet
        $display("\n--- Ethernet Frame ---");
        eth = new();
        repeat(3) begin
            assert(eth.randomize());
            $display("dst=%012h, src=%012h, type=0x%04h, len=%0d, fcs=0x%08h",
                    eth.dest_mac, eth.src_mac, eth.ethertype, 
                    eth.payload.size(), eth.fcs);
        end
    end
    
endmodule

/*
 * PROTOCOL CONSTRAINT PATTERNS:
 * 
 * KEY PRINCIPLES:
 * 1. Address alignment per protocol rules
 * 2. Burst/transfer size relationships
 * 3. Boundary crossing restrictions
 * 4. Valid field combinations
 * 5. Protocol-specific encodings
 * 
 * COMMON PATTERNS:
 * - Size -> Alignment: larger transfers need more alignment
 * - Burst -> Boundary: wrap bursts have alignment rules
 * - Type -> Fields: field validity depends on transaction type
 * - BE -> Data: byte enables affect data validity
 * 
 * VERIFICATION STRATEGY:
 * - Test all valid combinations
 * - Corner cases (max length, wrap boundaries)
 * - Protocol-specific violations (if testing error handling)
 * - Cross-protocol scenarios (AXI-APB bridge, etc.)
 */
