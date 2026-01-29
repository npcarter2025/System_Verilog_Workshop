// Power-Aware Testbench
// Verifies functionality across different power states

module power_aware_tb;

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Power control
    logic power_en;
    logic save;
    logic restore;
    logic iso_en;
    
    // DUT signals
    logic [31:0] data_in;
    logic [31:0] data_out;
    logic        valid;
    
    // Power states
    typedef enum logic [1:0] {
        PWR_ACTIVE   = 2'b00,
        PWR_SAVING   = 2'b01,
        PWR_DOWN     = 2'b10,
        PWR_RESTORING = 2'b11
    } power_state_t;
    
    power_state_t power_state;
    
    // ============================================
    // CLOCK GENERATION
    // ============================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // ============================================
    // TEST SEQUENCE
    // ============================================
    
    initial begin
        // Initialize
        rst_n = 0;
        power_en = 1;
        save = 0;
        restore = 0;
        iso_en = 0;
        data_in = 0;
        power_state = PWR_ACTIVE;
        
        // Reset
        #100;
        rst_n = 1;
        #50;
        
        // Test 1: Normal operation
        $display("Test 1: Normal operation");
        data_in = 32'hDEADBEEF;
        valid = 1;
        #100;
        
        // Test 2: Power-down sequence
        $display("Test 2: Power-down sequence");
        power_state = PWR_SAVING;
        save = 1;  // Save state
        #10;
        save = 0;
        
        iso_en = 1;  // Enable isolation
        #10;
        
        power_en = 0;  // Power off
        power_state = PWR_DOWN;
        #100;
        
        // Test 3: Power-up sequence
        $display("Test 3: Power-up sequence");
        power_state = PWR_RESTORING;
        power_en = 1;  // Power on
        #50;
        
        restore = 1;  // Restore state
        #10;
        restore = 0;
        
        iso_en = 0;  // Disable isolation
        power_state = PWR_ACTIVE;
        #50;
        
        // Verify restored data
        if (data_out == 32'hDEADBEEF)
            $display("PASS: Data correctly retained");
        else
            $display("FAIL: Data lost");
        
        $finish;
    end
    
    // ============================================
    // MONITORS AND CHECKERS
    // ============================================
    
    // Monitor power state transitions
    always @(power_state) begin
        $display("@%0t: Power state changed to %s", 
                $time, power_state.name());
    end
    
    // Check for X propagation
    always @(data_out) begin
        if ($isunknown(data_out) && power_state == PWR_ACTIVE) begin
            $error("X detected on data_out in ACTIVE state!");
        end
    end
    
    // Monitor power sequence
    property power_down_sequence;
        @(posedge clk)
        $fell(power_en) |-> $past(iso_en) && $past(save);
    endproperty
    
    a_pwr_down: assert property (power_down_sequence)
        else $error("Power-down sequence violation");

endmodule
