// ============================================================================
// inline_constraints.sv - Inline Randomization with {}
// ============================================================================

module inline_constraints;
    
    class packet;
        rand bit [7:0] addr;
        rand bit [31:0] data;
        rand bit [1:0] size;
        
        // Built-in constraints
        constraint addr_c {
            addr inside {[0:127]};
        }
        
        constraint size_c {
            size inside {1, 2, 4};
        }
    endclass
    
    // Class with no constraints (completely flexible)
    class flexible_packet;
        rand bit [15:0] value1;
        rand bit [15:0] value2;
        rand bit [1:0] cmd;
    endclass
    
    // Complex class for advanced inline constraints
    class transaction;
        rand bit [31:0] addr;
        rand bit [31:0] data;
        rand bit [3:0] burst_len;
        rand bit write;
        
        constraint basic_c {
            burst_len inside {[1:16]};
        }
    endclass
    
    initial begin
        packet pkt;
        flexible_packet flex;
        transaction tr;
        
        $display("=== Inline Constraint Examples ===\n");
        
        pkt = new();
        flex = new();
        tr = new();
        
        // ====================================================================
        // BASIC INLINE CONSTRAINTS
        // ====================================================================
        
        $display("--- Basic Inline Constraints ---");
        
        // Override built-in constraints
        repeat(3) begin
            assert(pkt.randomize() with {
                addr inside {[100:110]};
                data < 32'h100;
            });
            $display("addr=%0d, data=0x%0h, size=%0d", pkt.addr, pkt.data, pkt.size);
        end
        
        // Completely unconstrained randomization
        $display("\n--- Fully Random ---");
        repeat(3) begin
            assert(flex.randomize());
            $display("value1=0x%0h, value2=0x%0h, cmd=%0d", 
                    flex.value1, flex.value2, flex.cmd);
        end
        
        // ====================================================================
        // SPECIFIC VALUE CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Specific Values ---");
        
        // Fixed value
        assert(pkt.randomize() with {
            addr == 42;
            size == 2;
        });
        $display("Fixed: addr=%0d, size=%0d", pkt.addr, pkt.size);
        
        // Multiple specific values (choose one)
        repeat(3) begin
            assert(pkt.randomize() with {
                addr inside {10, 20, 30, 40};
            });
            $display("Specific set: addr=%0d", pkt.addr);
        end
        
        // ====================================================================
        // RELATIONAL CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Relational Constraints ---");
        
        // Between two variables
        repeat(3) begin
            assert(flex.randomize() with {
                value2 == value1 * 2;
                value1 inside {[10:50]};
            });
            $display("value1=%0d, value2=%0d (value2 = 2*value1)", 
                    flex.value1, flex.value2);
        end
        
        // Complex relationship
        repeat(3) begin
            assert(flex.randomize() with {
                value1 + value2 == 1000;
                value1 > value2;
            });
            $display("value1=%0d, value2=%0d (sum=1000, v1>v2)", 
                    flex.value1, flex.value2);
        end
        
        // ====================================================================
        // CONDITIONAL INLINE CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Conditional Constraints ---");
        
        // If-then constraint
        repeat(3) begin
            assert(tr.randomize() with {
                if (write)
                    data != 0;
                else
                    data == 0;
            });
            $display("write=%0b, data=0x%0h", tr.write, tr.data);
        end
        
        // Implication
        repeat(3) begin
            assert(tr.randomize() with {
                (burst_len > 4) -> (addr[2:0] == 3'b000);  // Aligned for bursts
            });
            $display("burst_len=%0d, addr=0x%0h (aligned=%0b)", 
                    tr.burst_len, tr.addr, (tr.addr[2:0] == 0));
        end
        
        // ====================================================================
        // ARRAY CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Array Inline Constraints ---");
        
        begin
            bit [7:0] arr[10];
            
            // Ascending array
            assert(std::randomize(arr) with {
                foreach(arr[i])
                    if (i > 0)
                        arr[i] > arr[i-1];
            });
            $write("Ascending: ");
            foreach(arr[i]) $write("%0d ", arr[i]);
            $display("");
            
            // All elements unique
            assert(std::randomize(arr) with {
                foreach(arr[i])
                    foreach(arr[j])
                        if (i != j)
                            arr[i] != arr[j];
            });
            $write("Unique: ");
            foreach(arr[i]) $write("%0d ", arr[i]);
            $display("");
        end
        
        // ====================================================================
        // DISTRIBUTION INLINE CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Distribution Constraints ---");
        
        repeat(5) begin
            assert(pkt.randomize() with {
                addr dist {
                    [0:31] := 70,
                    [32:63] := 20,
                    [64:127] := 10
                };
            });
            $display("Weighted addr=%0d", pkt.addr);
        end
        
        // ====================================================================
        // FUNCTIONAL CONSTRAINTS
        // ====================================================================
        
        $display("\n--- Functional Constraints ---");
        
        // Using $countones
        repeat(3) begin
            assert(flex.randomize() with {
                $countones(value1) == 4;  // Exactly 4 bits set
            });
            $display("value1=0x%0h (popcount=%0d)", 
                    flex.value1, $countones(flex.value1));
        end
        
        // Using modulo
        repeat(3) begin
            assert(pkt.randomize() with {
                addr % 16 == 0;  // Multiple of 16
            });
            $display("addr=%0d (aligned to 16)", pkt.addr);
        end
        
        // ====================================================================
        // MULTIPLE CONSTRAINTS COMBINED
        // ====================================================================
        
        $display("\n--- Combined Constraints ---");
        
        repeat(3) begin
            assert(tr.randomize() with {
                // Alignment
                addr[1:0] == 2'b00;
                
                // Range
                addr inside {[32'h1000:32'h1FFF]};
                
                // Write-specific
                if (write) {
                    data != 0;
                    burst_len inside {[1:4]};
                } else {
                    burst_len == 1;
                }
                
                // Even address for bursts
                (burst_len > 1) -> (addr[3:0] == 4'h0);
            });
            $display("write=%0b, addr=0x%0h, data=0x%0h, burst=%0d",
                    tr.write, tr.addr, tr.data, tr.burst_len);
        end
        
        // ====================================================================
        // RANDOMIZE SCOPE VARIABLES
        // ====================================================================
        
        $display("\n--- Standalone Variable Randomization ---");
        
        begin
            int x, y;
            
            assert(std::randomize(x, y) with {
                x inside {[1:10]};
                y inside {[1:10]};
                x + y == 15;
            });
            $display("x=%0d, y=%0d (sum=15)", x, y);
        end
    end
    
endmodule

/*
 * INLINE CONSTRAINT SYNTAX:
 * 
 * randomize() with { constraint_expression; }
 * 
 * CAPABILITIES:
 * 1. Override class constraints
 * 2. Add temporary constraints
 * 3. Combine multiple constraint types
 * 4. Use local variables in constraints
 * 5. Call randomize on scope variables
 * 
 * ADVANTAGES:
 * - No need to modify class
 * - Quick one-off constraints
 * - Test-specific randomization
 * - Override without inheritance
 * 
 * LIMITATIONS:
 * - Cannot reference class constraints by name
 * - More verbose than constraint blocks
 * - Harder to reuse across tests
 * 
 * BEST PRACTICES:
 * 1. Use for test-specific scenarios
 * 2. Keep inline constraints simple
 * 3. Complex constraints -> class constraint
 * 4. Document non-obvious constraints
 * 5. Use meaningful variable names
 * 
 * COMMON PATTERNS:
 * - Directed testing: randomize() with {field == value;}
 * - Corner cases: randomize() with {field == MAX;}
 * - Relationships: randomize() with {a + b == c;}
 * - Conditional: randomize() with {if (x) y == 0;}
 */
