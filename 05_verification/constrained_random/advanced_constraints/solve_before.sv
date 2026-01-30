// ============================================================================
// solve_before.sv - Solve Before Constraint Ordering
// ============================================================================

module solve_before;
    
    // Without solve...before, all variables randomized simultaneously
    class unordered_packet;
        rand bit [7:0] length;
        rand bit [7:0] data[];
        
        constraint length_c {
            length inside {[4:16]};
        }
        
        constraint data_c {
            data.size() == length;
        }
        
        // Problem: Solver may struggle with circular dependency
    endclass
    
    // With solve...before, explicit ordering
    class ordered_packet;
        rand bit [7:0] length;
        rand bit [7:0] data[];
        
        constraint length_c {
            length inside {[4:16]};
        }
        
        constraint data_c {
            data.size() == length;
        }
        
        // Solve length first, then data array
        constraint solve_order_c {
            solve length before data;
        }
    endclass
    
    // Complex example with dependencies
    class address_packet;
        rand bit [31:0] base_addr;
        rand bit [31:0] offset;
        rand bit [31:0] final_addr;
        rand bit [1:0] burst_size;
        
        constraint addr_calc_c {
            final_addr == base_addr + offset;
            base_addr[1:0] == 2'b00;  // Word aligned
        }
        
        constraint offset_c {
            offset < (1 << (burst_size + 2));
        }
        
        // Solve in order: burst_size -> base_addr -> offset -> final_addr
        constraint solve_order_c {
            solve burst_size before offset;
            solve base_addr before final_addr;
            solve offset before final_addr;
        }
    endclass
    
    // Performance optimization example
    class protocol_packet;
        rand bit [3:0] opcode;
        rand bit [7:0] length;
        rand bit [15:0] payload[];
        rand bit [15:0] checksum;
        
        constraint length_c {
            length inside {[8:64]};
            payload.size() == length;
        }
        
        constraint checksum_c {
            checksum == payload.sum() with (int'(item));
        }
        
        // Solve payload before checksum for efficiency
        constraint solve_order_c {
            solve length before payload;
            solve payload before checksum;
        }
    endclass
    
    // Multiple solve...before statements
    class complex_packet;
        rand bit [1:0] type_field;
        rand bit [7:0] size;
        rand bit [7:0] priority;
        rand bit [31:0] data[];
        
        constraint type_c {
            type_field inside {0, 1, 2};
        }
        
        constraint size_c {
            if (type_field == 0)
                size inside {[4:8]};
            else if (type_field == 1)
                size inside {[16:32]};
            else
                size inside {[64:128]};
            
            data.size() == size;
        }
        
        constraint priority_c {
            priority < size;
        }
        
        // Chain of dependencies
        constraint solve_order_c {
            solve type_field before size;
            solve size before data;
            solve size before priority;
        }
    endclass
    
    // Conditional solve order
    class adaptive_packet;
        rand bit mode;
        rand bit [15:0] addr;
        rand bit [15:0] mask;
        rand bit [15:0] result;
        
        constraint mode_c {
            mode inside {0, 1};
        }
        
        constraint calc_c {
            if (mode == 0)
                result == addr & mask;
            else
                result == addr | mask;
        }
        
        constraint solve_order_c {
            solve mode before addr;
            solve addr, mask before result;
        }
    endclass
    
    initial begin
        unordered_packet unpkt;
        ordered_packet ordpkt;
        address_packet addrpkt;
        protocol_packet protpkt;
        complex_packet complexpkt;
        
        $display("=== Solve Before Examples ===\n");
        
        // Unordered (may be slower)
        $display("--- Unordered Packet ---");
        unpkt = new();
        repeat(3) begin
            assert(unpkt.randomize());
            $display("length=%0d, data.size=%0d", unpkt.length, unpkt.data.size());
        end
        
        // Ordered (typically faster and more predictable)
        $display("\n--- Ordered Packet ---");
        ordpkt = new();
        repeat(3) begin
            assert(ordpkt.randomize());
            $display("length=%0d, data.size=%0d", ordpkt.length, ordpkt.data.size());
        end
        
        // Complex dependencies
        $display("\n--- Address Packet ---");
        addrpkt = new();
        repeat(3) begin
            assert(addrpkt.randomize());
            $display("burst=%0d, base=0x%0h, offset=0x%0h, final=0x%0h",
                    addrpkt.burst_size, addrpkt.base_addr, 
                    addrpkt.offset, addrpkt.final_addr);
        end
        
        // Checksum calculation
        $display("\n--- Protocol Packet ---");
        protpkt = new();
        repeat(2) begin
            assert(protpkt.randomize());
            $display("length=%0d, checksum=0x%0h", protpkt.length, protpkt.checksum);
        end
        
        // Multiple dependencies
        $display("\n--- Complex Packet ---");
        complexpkt = new();
        repeat(3) begin
            assert(complexpkt.randomize());
            $display("type=%0d, size=%0d, priority=%0d, data.size=%0d",
                    complexpkt.type_field, complexpkt.size, 
                    complexpkt.priority, complexpkt.data.size());
        end
    end
    
endmodule

/*
 * SOLVE BEFORE GUIDELINES:
 * 
 * WHEN TO USE:
 * 1. Dependent variables (one depends on another)
 * 2. Performance optimization
 * 3. Reduce solver complexity
 * 4. Make randomization more predictable
 * 
 * SYNTAX:
 *   solve var1 before var2;
 *   solve var1, var2 before var3;
 * 
 * BENEFITS:
 * - Faster randomization
 * - More predictable results
 * - Easier to debug constraint failures
 * - Better solver efficiency
 * 
 * COMMON PATTERNS:
 * 1. Size before array: solve length before data;
 * 2. Type before size: solve type before length;
 * 3. Inputs before outputs: solve a, b before result;
 * 4. Mode before config: solve mode before settings;
 * 
 * WARNINGS:
 * - Over-constraining can make code brittle
 * - Only use when there's actual dependency
 * - Don't create circular dependencies
 */
