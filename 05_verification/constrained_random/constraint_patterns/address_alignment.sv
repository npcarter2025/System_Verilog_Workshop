// ============================================================================
// address_alignment.sv - Address Alignment Constraint Patterns
// ============================================================================

module address_alignment;
    
    // Word-aligned addresses (4-byte aligned)
    class word_aligned_addr;
        rand bit [31:0] addr;
        
        constraint word_align_c {
            addr[1:0] == 2'b00;
        }
    endclass
    
    // Configurable alignment
    class aligned_addr;
        rand bit [31:0] addr;
        int alignment;  // 1, 2, 4, 8, 16, etc.
        
        function new(int align = 4);
            alignment = align;
        endfunction
        
        constraint align_c {
            (alignment == 1)  -> (addr[0:0] == 1'b0);
            (alignment == 2)  -> (addr[1:0] == 2'b00);
            (alignment == 4)  -> (addr[2:0] == 3'b000);
            (alignment == 8)  -> (addr[3:0] == 4'h0);
            (alignment == 16) -> (addr[4:0] == 5'h0);
            (alignment == 32) -> (addr[5:0] == 6'h0);
        }
    endclass
    
    // Page-aligned addresses
    class page_aligned_addr;
        rand bit [31:0] addr;
        int page_size;  // 4KB, 2MB, 1GB, etc.
        
        function new(int psize = 4096);
            page_size = psize;
        endfunction
        
        constraint page_align_c {
            (page_size == 4096)    -> (addr[11:0] == 12'h0);  // 4KB
            (page_size == 2097152) -> (addr[20:0] == 21'h0);  // 2MB
            (page_size == 1073741824) -> (addr[29:0] == 30'h0);  // 1GB
        }
    endclass
    
    // Cache line aligned (typically 64 bytes)
    class cache_line_addr;
        rand bit [31:0] addr;
        
        constraint cache_align_c {
            addr[5:0] == 6'h0;  // 64-byte aligned
        }
    endclass
    
    // Burst-aligned addresses
    class burst_addr;
        rand bit [31:0] addr;
        rand bit [3:0] burst_length;  // 1, 2, 4, 8, 16
        rand bit [1:0] burst_size;    // 1, 2, 4, 8 bytes per beat
        
        constraint burst_length_c {
            burst_length inside {1, 2, 4, 8, 16};
        }
        
        constraint burst_size_c {
            burst_size inside {0, 1, 2, 3};  // 1B, 2B, 4B, 8B
        }
        
        // Address must be aligned to burst boundary
        constraint burst_align_c {
            // Total burst size = burst_length * (1 << burst_size)
            // Address alignment = total burst size
            
            (burst_size == 0) -> (addr[0:0] == 1'b0);  // 1-byte
            (burst_size == 1) -> (addr[1:0] == 2'b00); // 2-byte
            (burst_size == 2) -> (addr[2:0] == 3'b000); // 4-byte
            (burst_size == 3) -> (addr[3:0] == 4'h0);  // 8-byte
            
            // Additional alignment for longer bursts
            (burst_length >= 4 && burst_size >= 2) -> (addr[4:0] == 5'h0);
            (burst_length >= 8 && burst_size >= 2) -> (addr[5:0] == 6'h0);
            (burst_length == 16 && burst_size >= 2) -> (addr[6:0] == 7'h0);
        }
    endclass
    
    // Range with alignment
    class range_aligned_addr;
        rand bit [31:0] addr;
        bit [31:0] start_addr;
        bit [31:0] end_addr;
        int alignment;
        
        function new(bit [31:0] start = 32'h1000, 
                    bit [31:0] end = 32'h2000,
                    int align = 4);
            start_addr = start;
            end_addr = end;
            alignment = align;
        endfunction
        
        constraint range_c {
            addr >= start_addr;
            addr <= end_addr;
        }
        
        constraint align_c {
            (alignment == 4) -> (addr[1:0] == 2'b00);
            (alignment == 8) -> (addr[2:0] == 3'b000);
            (alignment == 16) -> (addr[3:0] == 4'h0);
        }
    endclass
    
    // Non-crossing boundary addresses
    class boundary_safe_addr;
        rand bit [31:0] addr;
        rand bit [7:0] transfer_size;
        int boundary;  // e.g., 4KB boundary
        
        function new(int bound = 4096);
            boundary = bound;
        endfunction
        
        constraint size_c {
            transfer_size inside {[1:256]};
        }
        
        // Transfer must not cross boundary
        constraint no_cross_c {
            ((addr / boundary) == ((addr + transfer_size - 1) / boundary));
        }
    endclass
    
    // AXI-style address alignment
    class axi_addr;
        rand bit [31:0] addr;
        rand bit [2:0] size;     // AxSIZE: 2^size bytes per beat
        rand bit [7:0] length;   // AxLEN: length+1 beats
        
        constraint size_c {
            size inside {[0:3]};  // 1, 2, 4, 8 bytes
        }
        
        constraint length_c {
            length inside {[0:15]};  // 1-16 beats
        }
        
        // Start address aligned to transfer size
        constraint addr_align_c {
            (size == 0) -> (addr[0:0] == 1'b0);
            (size == 1) -> (addr[1:0] == 2'b00);
            (size == 2) -> (addr[2:0] == 3'b000);
            (size == 3) -> (addr[3:0] == 4'h0);
        }
        
        // Narrow transfers must stay within 4KB boundary
        constraint narrow_boundary_c {
            (size < 3) -> (
                (addr[11:0] + ((length + 1) * (1 << size))) <= 12'h1000
            );
        }
    endclass
    
    // Multiple of N addresses
    class multiple_of_addr;
        rand bit [31:0] addr;
        int multiple;
        
        function new(int mult = 64);
            multiple = mult;
        endfunction
        
        constraint multiple_c {
            (addr % multiple) == 0;
        }
    endclass
    
    initial begin
        word_aligned_addr word_addr;
        aligned_addr align4, align16;
        page_aligned_addr page_addr;
        cache_line_addr cache_addr;
        burst_addr burst;
        range_aligned_addr range_addr;
        boundary_safe_addr boundary_addr;
        axi_addr axi;
        multiple_of_addr mult64;
        
        $display("=== Address Alignment Patterns ===\n");
        
        // Word aligned
        $display("--- Word Aligned (4-byte) ---");
        word_addr = new();
        repeat(5) begin
            assert(word_addr.randomize());
            $display("0x%08h (last 2 bits: %02b)", 
                    word_addr.addr, word_addr.addr[1:0]);
        end
        
        // Configurable alignment
        $display("\n--- 16-byte Alignment ---");
        align16 = new(16);
        repeat(5) begin
            assert(align16.randomize());
            $display("0x%08h (last 4 bits: %04b)",
                    align16.addr, align16.addr[3:0]);
        end
        
        // Page aligned
        $display("\n--- Page Aligned (4KB) ---");
        page_addr = new(4096);
        repeat(3) begin
            assert(page_addr.randomize());
            $display("0x%08h", page_addr.addr);
        end
        
        // Cache line
        $display("\n--- Cache Line Aligned (64-byte) ---");
        cache_addr = new();
        repeat(5) begin
            assert(cache_addr.randomize());
            $display("0x%08h", cache_addr.addr);
        end
        
        // Burst aligned
        $display("\n--- Burst Aligned ---");
        burst = new();
        repeat(5) begin
            assert(burst.randomize());
            $display("addr=0x%08h, len=%0d, size=%0d bytes",
                    burst.addr, burst.burst_length, (1 << burst.burst_size));
        end
        
        // Range with alignment
        $display("\n--- Range + Alignment ---");
        range_addr = new(32'h1000, 32'h2000, 16);
        repeat(5) begin
            assert(range_addr.randomize());
            $display("0x%08h (in range 0x1000-0x2000, 16-byte aligned)",
                    range_addr.addr);
        end
        
        // Boundary safe
        $display("\n--- Boundary Safe (4KB) ---");
        boundary_addr = new(4096);
        repeat(5) begin
            assert(boundary_addr.randomize());
            $display("addr=0x%08h, size=%0d, end=0x%08h",
                    boundary_addr.addr, 
                    boundary_addr.transfer_size,
                    boundary_addr.addr + boundary_addr.transfer_size - 1);
        end
        
        // AXI-style
        $display("\n--- AXI Address Alignment ---");
        axi = new();
        repeat(5) begin
            assert(axi.randomize());
            $display("addr=0x%08h, size=%0dB, beats=%0d",
                    axi.addr, (1 << axi.size), axi.length + 1);
        end
        
        // Multiple of 64
        $display("\n--- Multiple of 64 ---");
        mult64 = new(64);
        repeat(5) begin
            assert(mult64.randomize());
            $display("0x%08h (%0d)", mult64.addr, mult64.addr);
        end
    end
    
endmodule

/*
 * ADDRESS ALIGNMENT PATTERNS:
 * 
 * COMMON ALIGNMENTS:
 * - Byte:       No alignment (addr[0:0] can be anything)
 * - Half-word:  2-byte aligned (addr[0:0] == 0)
 * - Word:       4-byte aligned (addr[1:0] == 00)
 * - Double:     8-byte aligned (addr[2:0] == 000)
 * - Cache line: 64-byte aligned (addr[5:0] == 000000)
 * - Page:       4KB aligned (addr[11:0] == 0)
 * 
 * WHY ALIGNMENT MATTERS:
 * 1. Hardware performance (aligned accesses faster)
 * 2. Protocol requirements (AXI, AHB, etc.)
 * 3. Cache efficiency
 * 4. DMA restrictions
 * 5. Memory interface requirements
 * 
 * CONSTRAINT TECHNIQUES:
 * 1. Bit masking: addr[N:0] == 0
 * 2. Modulo: (addr % N) == 0
 * 3. Division check: (addr / N) * N == addr
 * 4. Conditional on transfer size
 * 
 * TESTING STRATEGY:
 * - Test aligned and unaligned (if supported)
 * - Boundary conditions (crossing page boundaries)
 * - Various alignment requirements
 * - Protocol-specific rules
 */
