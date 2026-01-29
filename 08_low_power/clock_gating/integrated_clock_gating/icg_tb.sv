// Testbench for Integrated Clock Gating Cell
// Verifies glitch-free operation and proper enable timing

module icg_tb;

    logic clk;
    logic en;
    logic test_en;
    logic gclk;
    
    // Instantiate DUT
    icg_cell dut (
        .clk(clk),
        .en(en),
        .test_en(test_en),
        .gclk(gclk)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Glitch detection
    logic glitch_detected;
    integer edge_count;
    
    always @(gclk) begin
        if ($time > 0) begin
            edge_count = edge_count + 1;
            // Check for glitches (multiple edges in short time)
            #1;
            if (edge_count > 1) begin
                glitch_detected = 1;
                $error("GLITCH DETECTED at time %0t", $time);
            end
            edge_count = 0;
        end
    end
    
    // Test sequence
    initial begin
        $dumpfile("icg_tb.vcd");
        $dumpvars(0, icg_tb);
        
        // Initialize
        en = 0;
        test_en = 0;
        glitch_detected = 0;
        edge_count = 0;
        
        // Wait for clock stabilization
        repeat(5) @(posedge clk);
        
        // Test 1: Enable during high phase (should not glitch)
        $display("Test 1: Enable during clock high");
        @(posedge clk);
        #2 en = 1;  // Change during high phase
        repeat(5) @(posedge clk);
        assert(!glitch_detected) else $error("Test 1 failed");
        
        // Test 2: Disable during high phase
        $display("Test 2: Disable during clock high");
        @(posedge clk);
        #2 en = 0;
        repeat(5) @(posedge clk);
        
        // Test 3: Multiple enable/disable cycles
        $display("Test 3: Multiple cycles");
        repeat(10) begin
            @(negedge clk);
            en = ~en;
            repeat(3) @(posedge clk);
        end
        
        // Test 4: Test mode bypass
        $display("Test 4: Test mode");
        en = 0;
        test_en = 1;
        repeat(5) @(posedge clk);
        assert(gclk == clk) else $error("Test mode not bypassing");
        
        // Test 5: Rapid enable toggles
        $display("Test 5: Rapid toggles");
        test_en = 0;
        repeat(20) begin
            @(negedge clk);
            en = $random;
        end
        
        if (!glitch_detected)
            $display("ALL TESTS PASSED - No glitches detected");
        else
            $display("TESTS FAILED - Glitches detected");
        
        #100;
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        $display("@%0t: en=%b test_en=%b gclk=%b", 
                $time, en, test_en, gclk);
    end

endmodule
