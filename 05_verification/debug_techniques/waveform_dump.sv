// ============================================================================
// waveform_dump.sv - Waveform Dumping Techniques for Debug
// ============================================================================

module waveform_dump;
    
    logic clk, rst_n;
    logic [31:0] data_a, data_b, result;
    logic valid, ready;
    
    // ========================================================================
    // Method 1: VCD (Value Change Dump) - Universal Format
    // ========================================================================
    initial begin
        // Basic VCD dump
        $dumpfile("waves.vcd");
        $dumpvars(0, waveform_dump);  // 0 = dump all hierarchy
        
        // Explanation:
        // - Opens file "waves.vcd"
        // - Dumps all variables in module waveform_dump and below
        // - 0 means unlimited depth
        // - Works with all simulators
    end
    
    // ========================================================================
    // Method 2: Selective VCD Dumping
    // ========================================================================
    initial begin
        $dumpfile("selective.vcd");
        
        // Dump specific signals only
        $dumpvars(1, waveform_dump);  // Level 1 only (this module)
        $dumpvars(0, data_a);          // Specific signal, all bits
        $dumpvars(0, result);           // Another specific signal
        
        // Don't dump other signals - reduces file size
    end
    
    // ========================================================================
    // Method 3: Time-Limited Dumping
    // ========================================================================
    initial begin
        $dumpfile("time_limited.vcd");
        
        // Start dumping at specific time
        #100ns $dumpvars(0, waveform_dump);
        
        // Stop dumping at specific time
        #1000ns $dumpoff;
        
        // Resume dumping
        #500ns $dumpon;
        
        // Final stop
        #1000ns $dumpoff;
        
        $display("Dumping windows: 100-1100ns and 1600-2600ns");
    end
    
    // ========================================================================
    // Method 4: FSDBDump (Verdi/DVE - FSDB Format)
    // ========================================================================
    initial begin
        // FSDB is more efficient than VCD for large designs
        // $fsdbDumpfile("waves.fsdb");
        // $fsdbDumpvars(0, waveform_dump);
        
        // Additional FSDB options:
        // $fsdbDumpvars("+mda");  // Multi-dimensional arrays
        // $fsdbDumpvars("+struct");  // Structures
        // $fsdbDumpvars("+packedmda");  // Packed arrays
        
        $display("FSDB dumping (commented out - requires Verdi)");
    end
    
    // ========================================================================
    // Method 5: VPD (VCS - VPD Format)
    // ========================================================================
    initial begin
        // VPD is Synopsys VCS format
        // $vcdpluson;  // Start VPD dumping
        // $vcdplusoff;  // Stop VPD dumping
        
        $display("VPD dumping (commented out - requires VCS)");
    end
    
    // ========================================================================
    // Method 6: Conditional Dumping Based on Events
    // ========================================================================
    event start_debug, stop_debug;
    
    initial begin
        $dumpfile("conditional.vcd");
        
        // Wait for trigger to start dumping
        @(start_debug);
        $dumpvars(0, waveform_dump);
        $display("[%0t] Started waveform dumping", $time);
        
        // Wait for trigger to stop
        @(stop_debug);
        $dumpoff;
        $display("[%0t] Stopped waveform dumping", $time);
    end
    
    // ========================================================================
    // Method 7: Hierarchical Selective Dumping
    // ========================================================================
    module sub_module_a;
        logic [15:0] internal_sig;
        logic state;
    endmodule
    
    module sub_module_b;
        logic [7:0] counter;
        logic overflow;
    endmodule
    
    sub_module_a sma();
    sub_module_b smb();
    
    initial begin
        $dumpfile("hierarchical.vcd");
        
        // Dump only sub_module_a
        $dumpvars(0, sma);
        
        // Don't dump sub_module_b (maybe too verbose)
        
        $display("Only dumping sub_module_a");
    end
    
    // ========================================================================
    // Method 8: Signal-Specific Dumping with Filters
    // ========================================================================
    initial begin
        $dumpfile("filtered.vcd");
        
        // Dump only when certain conditions met
        fork
            begin
                wait(valid && ready);
                $dumpvars(0, waveform_dump);
                $display("[%0t] Dumping started (valid & ready)", $time);
            end
        join_none
    end
    
    // ========================================================================
    // Method 9: Multiple VCD Files (Different Scenarios)
    // ========================================================================
    initial begin
        // Test phase 1
        $dumpfile("phase1.vcd");
        $dumpvars(0, waveform_dump);
        #500ns;
        $dumpoff;
        $dumpflush;  // Flush and close
        
        // Test phase 2
        #100ns;
        $dumpfile("phase2.vcd");
        $dumpvars(0, waveform_dump);
        #500ns;
        $dumpoff;
        
        $display("Created separate waveform files for each phase");
    end
    
    // ========================================================================
    // Method 10: Array and Memory Dumping
    // ========================================================================
    logic [31:0] memory [0:255];
    logic [7:0] packet_buffer [0:1023];
    
    initial begin
        $dumpfile("arrays.vcd");
        
        // Dump entire array
        $dumpvars(0, memory);
        
        // Dump specific array elements
        $dumpvars(0, memory[0]);
        $dumpvars(0, memory[10]);
        $dumpvars(0, memory[255]);
        
        // For large arrays, consider selective dumping
        $display("Dumping memory arrays");
    end
    
    // ========================================================================
    // Best Practices Example
    // ========================================================================
    initial begin
        // Combined best practices
        $dumpfile("best_practice.vcd");
        
        // Wait for reset to complete
        wait(rst_n == 1);
        @(posedge clk);
        
        // Start dumping after reset
        $dumpvars(0, waveform_dump);
        $display("[%0t] Waveform dumping started", $time);
        
        // Auto-stop after reasonable time
        #10000ns;
        $dumpoff;
        $display("[%0t] Waveform dumping stopped", $time);
    end
    
    // ========================================================================
    // Simulation Control and Waveform Management
    // ========================================================================
    initial begin
        $dumpfile("managed.vcd");
        
        // Dump with management
        $dumpvars(0, waveform_dump);
        
        // Periodically flush to disk (prevents loss on crash)
        fork
            forever begin
                #1000ns;
                $dumpflush;  // Write buffered data to file
            end
        join_none
        
        // Limit file size by stopping after time
        #50000ns;
        $dumpoff;
        $display("Waveform limited to 50us to control file size");
    end
    
    // ========================================================================
    // Debug-on-Demand (Trigger-Based Dumping)
    // ========================================================================
    logic error_detected;
    
    initial begin
        $display("Waiting for error to trigger waveform dump...");
        
        // Only dump when error occurs
        @(posedge error_detected);
        
        // Dump for time window around error
        $dumpfile("error_window.vcd");
        $dumpvars(0, waveform_dump);
        $display("[%0t] ERROR DETECTED - Started dumping", $time);
        
        // Dump for 1000ns after error
        #1000ns;
        $dumpoff;
        $display("[%0t] Finished error window dump", $time);
    end
    
    // ========================================================================
    // Simple Test Logic
    // ========================================================================
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset
    initial begin
        rst_n = 0;
        #50 rst_n = 1;
    end
    
    // Simple activity for demonstration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_a <= 0;
            data_b <= 0;
            result <= 0;
            valid <= 0;
        end else begin
            data_a <= data_a + 1;
            data_b <= data_b + 2;
            result <= data_a + data_b;
            valid <= ~valid;
        end
    end
    
    assign ready = valid;
    
    // Trigger events
    initial begin
        #200 -> start_debug;
        #500 -> stop_debug;
    end
    
    // Simulate error
    initial begin
        error_detected = 0;
        #750 error_detected = 1;
        #10 error_detected = 0;
    end
    
    // Test control
    initial begin
        #2000;
        $display("\n=== Waveform Dumping Examples Complete ===");
        $finish;
    end
    
endmodule

/*
 * WAVEFORM DUMPING GUIDE:
 * 
 * FORMAT COMPARISON:
 * 
 * VCD (Value Change Dump):
 * + Universal format (all simulators)
 * + Human-readable ASCII
 * + Works with GTKWave, ModelSim, etc.
 * - Large file size
 * - Slower performance
 * 
 * FSDB (Fast Signal Database):
 * + Compact binary format
 * + Fast performance
 * + Verdi native format
 * - Requires Verdi/Debussy
 * 
 * VPD (VCS Plus Dump):
 * + Optimized for VCS
 * + Good performance
 * - VCS-specific
 * 
 * WLF (Waveform Log File):
 * + ModelSim/Questa native
 * + Good performance
 * - Tool-specific
 * 
 * BASIC COMMANDS:
 * 
 * $dumpfile("name.vcd");          // Open dump file
 * $dumpvars(depth, instance);     // Start dumping
 * $dumpon;                         // Resume dumping
 * $dumpoff;                        // Stop dumping
 * $dumpflush;                      // Flush buffer to disk
 * $dumpall;                        // Dump current values
 * 
 * DEPTH PARAMETER:
 * 0: Unlimited (all hierarchy)
 * 1: Current module only
 * 2: Current + 1 level down
 * etc.
 * 
 * BEST PRACTICES:
 * 
 * 1. File Size Management:
 *    - Dump only necessary signals
 *    - Use time windows
 *    - Stop dumping when not needed
 *    - Consider compressed formats
 * 
 * 2. Performance:
 *    - Don't dump entire design if not needed
 *    - Use selective dumping
 *    - Flush periodically for safety
 *    - Turn off when not debugging
 * 
 * 3. Debug Efficiency:
 *    - Start after reset completes
 *    - Dump around areas of interest
 *    - Use trigger-based dumping
 *    - Multiple files for different phases
 * 
 * 4. Automation:
 *    - Control via command line: +vcd, +fsdb
 *    - Environment variables
 *    - Conditional compilation
 * 
 * COMMON PATTERNS:
 * 
 * 1. Always Dump (Development):
 * initial begin
 *     $dumpfile("debug.vcd");
 *     $dumpvars(0, top);
 * end
 * 
 * 2. Conditional Dump (Regression):
 * initial begin
 *     if ($test$plusargs("dump"))
 *         $dumpfile("waves.vcd");
 *         $dumpvars(0, top);
 * end
 * 
 * 3. Error-Triggered Dump:
 * always @(error) begin
 *     if (error) begin
 *         $dumpfile("error.vcd");
 *         $dumpvars(0, top);
 *     end
 * end
 * 
 * 4. Window Dump:
 * initial begin
 *     #start_time $dumpvars(0, top);
 *     #duration $dumpoff;
 * end
 * 
 * VIEWING WAVEFORMS:
 * 
 * GTKWave (open source):
 * - gtkwave waves.vcd
 * - Free, cross-platform
 * 
 * ModelSim/Questa:
 * - vsim -view waves.wlf
 * - Commercial, powerful
 * 
 * Verdi:
 * - verdi -ssf waves.fsdb
 * - Commercial, advanced features
 * 
 * DVE (VCS):
 * - dve -vpd waves.vpd
 * - Commercial, VCS integration
 * 
 * TIPS FOR LARGE DESIGNS:
 * 
 * 1. Start with small scope, expand as needed
 * 2. Use hierarchical dumping strategically
 * 3. Dump only failing test cases
 * 4. Use compressed formats (FSDB)
 * 5. Clean up old waveform files
 * 6. Consider using assertions instead
 * 7. Profile what signals are actually viewed
 * 
 * DEBUGGING WORKFLOW:
 * 
 * 1. Run test without dump (check logs)
 * 2. If error, re-run with dump
 * 3. Use window around error
 * 4. Dump minimal signals first
 * 5. Add more signals as needed
 * 6. Turn off once fixed
 * 
 * COMMAND-LINE CONTROL:
 * 
 * vsim top +dump               // Enable
 * vsim top +dump +dump_start=1000  // Start time
 * vsim top +dump +dump_stop=2000   // Stop time
 * vsim top +vcd=waves.vcd      // Specific file
 * 
 * COMMON ISSUES:
 * 
 * ❌ Huge files (GB+)
 * ✅ Selective dumping, time windows
 * 
 * ❌ Slow simulation
 * ✅ Reduce dump scope, use FSDB
 * 
 * ❌ Missing signals
 * ✅ Check depth, instance path
 * 
 * ❌ File not found
 * ✅ Check permissions, disk space
 * 
 * PERFORMANCE IMPACT:
 * - No dump: 100% speed
 * - VCD small: 70-90% speed
 * - VCD large: 30-60% speed
 * - FSDB: 80-95% speed
 * 
 * Choose wisely based on needs!
 */
