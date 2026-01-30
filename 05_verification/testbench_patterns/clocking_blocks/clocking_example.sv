// ============================================================================
// clocking_example.sv - Clocking Block Examples and Best Practices
// ============================================================================

// ============================================================================
// Basic Clocking Block
// ============================================================================
interface basic_clk_if(input logic clk);
    logic [7:0] data;
    logic valid;
    logic ready;
    
    // Default clocking block
    default clocking cb @(posedge clk);
        default input #1ns output #1ns;
        output data, valid;
        input ready;
    endclocking
endinterface

// ============================================================================
// Clocking Block with Input/Output Skew
// ============================================================================
interface skewed_if(input logic clk);
    logic [31:0] addr;
    logic [31:0] data;
    logic req;
    logic ack;
    
    // Clocking block with explicit skews
    clocking testbench_cb @(posedge clk);
        default input #1ns output #0;
        
        // Sample inputs 1ns after clock edge
        input #1ns ack;
        input #1ns data;
        
        // Drive outputs just before clock edge
        output #0 addr;
        output #0 req;
    endclocking
    
    // Separate clocking block for monitoring
    clocking monitor_cb @(posedge clk);
        input #1ns addr, data, req, ack;
    endclocking
endinterface

// ============================================================================
// Multiple Clocking Blocks (Different Clock Domains)
// ============================================================================
interface multi_clock_if(input logic clk_a, input logic clk_b);
    logic [7:0] data_a;
    logic valid_a;
    
    logic [7:0] data_b;
    logic valid_b;
    
    // Clock domain A
    clocking cb_a @(posedge clk_a);
        default input #1ns output #1ns;
        output data_a, valid_a;
    endclocking
    
    // Clock domain B
    clocking cb_b @(posedge clk_b);
        default input #1ns output #1ns;
        input data_b, valid_b;
    endclocking
endinterface

// ============================================================================
// Clocking Block with Negedge
// ============================================================================
interface negedge_if(input logic clk);
    logic [15:0] addr;
    logic [31:0] data;
    logic strobe;
    
    // Posedge clocking
    clocking pos_cb @(posedge clk);
        output addr, data;
    endclocking
    
    // Negedge clocking (DDR-like)
    clocking neg_cb @(negedge clk);
        output strobe;
    endclocking
endinterface

// ============================================================================
// Clocking Block in Interface with Modports
// ============================================================================
interface full_if(input logic clk, input logic rst_n);
    logic [31:0] addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic we, re;
    logic ready;
    
    // Master clocking block
    clocking master_cb @(posedge clk);
        default input #1ns output #1ns;
        output addr, wdata, we, re;
        input rdata, ready;
    endclocking
    
    // Slave clocking block
    clocking slave_cb @(posedge clk);
        default input #1ns output #1ns;
        input addr, wdata, we, re;
        output rdata, ready;
    endclocking
    
    // Monitor clocking block
    clocking monitor_cb @(posedge clk);
        input #1ns addr, wdata, rdata, we, re, ready;
    endclocking
    
    // Modports with clocking blocks
    modport master (
        clocking master_cb,
        input rst_n
    );
    
    modport slave (
        clocking slave_cb,
        input rst_n
    );
    
    modport monitor (
        clocking monitor_cb,
        input rst_n
    );
endinterface

// ============================================================================
// Using Clocking Blocks in Classes (Testbench)
// ============================================================================
class driver_with_clocking;
    virtual full_if.master vif;
    
    function new(virtual full_if.master v);
        vif = v;
    endfunction
    
    task write(input logic [31:0] a, input logic [31:0] d);
        // Using clocking block for race-free driving
        @(vif.master_cb);
        vif.master_cb.addr <= a;
        vif.master_cb.wdata <= d;
        vif.master_cb.we <= 1'b1;
        vif.master_cb.re <= 1'b0;
        
        @(vif.master_cb);
        wait(vif.master_cb.ready == 1'b1);
        
        @(vif.master_cb);
        vif.master_cb.we <= 1'b0;
        
        $display("[DRIVER] Write: addr=0x%h, data=0x%h", a, d);
    endtask
    
    task read(input logic [31:0] a, output logic [31:0] d);
        @(vif.master_cb);
        vif.master_cb.addr <= a;
        vif.master_cb.re <= 1'b1;
        vif.master_cb.we <= 1'b0;
        
        @(vif.master_cb);
        wait(vif.master_cb.ready == 1'b1);
        d = vif.master_cb.rdata;  // Sample with input skew
        
        @(vif.master_cb);
        vif.master_cb.re <= 1'b0;
        
        $display("[DRIVER] Read: addr=0x%h, data=0x%h", a, d);
    endtask
endclass

// ============================================================================
// Wait for Clock Edges
// ============================================================================
class clock_waiter;
    virtual full_if.master vif;
    
    function new(virtual full_if.master v);
        vif = v;
    endfunction
    
    task wait_cycles(int n);
        repeat(n) @(vif.master_cb);
    endtask
    
    task wait_for_ready();
        @(vif.master_cb);
        while (vif.master_cb.ready != 1'b1)
            @(vif.master_cb);
    endtask
endclass

// ============================================================================
// Clocking Block with Event
// ============================================================================
interface event_if(input logic clk);
    logic [7:0] data;
    logic trigger;
    
    clocking cb @(posedge clk);
        output data;
        input trigger;
    endclocking
    
    // Can wait on clocking block events
    task wait_for_trigger();
        @(cb);
        while (!cb.trigger)
            @(cb);
    endtask
endinterface

// ============================================================================
// Cycle Delay Using ##
// ============================================================================
class cycle_delay_example;
    virtual full_if.master vif;
    
    function new(virtual full_if.master v);
        vif = v;
    endfunction
    
    task test_delays();
        // Wait 1 clock cycle
        ##1;
        $display("1 cycle passed");
        
        // Wait 5 clock cycles
        ##5;
        $display("5 cycles passed");
        
        // Equivalent to:
        // repeat(5) @(vif.master_cb);
    endtask
    
    task sampled_value_example();
        logic [31:0] prev_addr;
        
        // Sample current value
        prev_addr = vif.master_cb.addr;
        
        // Wait and sample again
        ##1;
        if (vif.master_cb.addr != prev_addr)
            $display("Address changed");
    endtask
endclass

// ============================================================================
// Clocking Block for Assertions
// ============================================================================
interface assertion_if(input logic clk, input logic rst_n);
    logic req;
    logic ack;
    logic [31:0] data;
    
    clocking cb @(posedge clk);
        input req, ack, data;
    endclocking
    
    // Use clocking block in assertions
    property req_ack_protocol;
        @(cb) disable iff (!rst_n)
        cb.req |-> ##[1:5] cb.ack;
    endproperty
    
    assert property (req_ack_protocol)
        else $error("Request not acknowledged within 5 cycles");
    
    // Sampled value in assertion
    property data_stable;
        @(cb) disable iff (!rst_n)
        (cb.req && !cb.ack) |=> $stable(cb.data);
    endproperty
    
    assert property (data_stable)
        else $error("Data changed before ack");
endinterface

// ============================================================================
// Simple DUT for Testing
// ============================================================================
module simple_memory (
    full_if.slave bus
);
    logic [31:0] mem[256];
    
    always_ff @(posedge bus.slave_cb) begin
        bus.slave_cb.ready <= 1'b0;
        bus.slave_cb.rdata <= 32'h0;
        
        if (bus.slave_cb.we) begin
            mem[bus.slave_cb.addr[7:0]] <= bus.slave_cb.wdata;
            ##1 bus.slave_cb.ready <= 1'b1;
        end
        
        if (bus.slave_cb.re) begin
            ##1 begin
                bus.slave_cb.rdata <= mem[bus.slave_cb.addr[7:0]];
                bus.slave_cb.ready <= 1'b1;
            end
        end
    end
endmodule

// ============================================================================
// Testbench
// ============================================================================
module clocking_example;
    logic clk, rst_n;
    
    // Interface with clocking blocks
    full_if dut_if(clk, rst_n);
    
    // DUT
    simple_memory dut(.bus(dut_if.slave));
    
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
    
    // Test using driver with clocking blocks
    initial begin
        driver_with_clocking drv;
        logic [31:0] read_data;
        
        drv = new(dut_if.master);
        
        @(posedge rst_n);
        repeat(5) @(posedge clk);
        
        $display("\n=== Clocking Block Examples ===\n");
        
        // Write tests
        drv.write(32'h10, 32'hDEADBEEF);
        drv.write(32'h20, 32'hCAFEBABE);
        drv.write(32'h30, 32'h12345678);
        
        // Read tests
        drv.read(32'h10, read_data);
        drv.read(32'h20, read_data);
        drv.read(32'h30, read_data);
        
        #200;
        $display("\n=== Test Complete ===\n");
        $finish;
    end
    
    // Monitor using clocking block
    initial begin
        @(posedge rst_n);
        
        forever begin
            @(dut_if.monitor_cb);
            
            if (dut_if.monitor_cb.we && dut_if.monitor_cb.ready) begin
                $display("[MONITOR] Write: addr=0x%h, data=0x%h", 
                        dut_if.monitor_cb.addr, 
                        dut_if.monitor_cb.wdata);
            end
            
            if (dut_if.monitor_cb.re && dut_if.monitor_cb.ready) begin
                $display("[MONITOR] Read: addr=0x%h, data=0x%h", 
                        dut_if.monitor_cb.addr, 
                        dut_if.monitor_cb.rdata);
            end
        end
    end
    
    // Waveform dump
    initial begin
        $dumpfile("clocking_example.vcd");
        $dumpvars(0, clocking_example);
    end
    
endmodule

/*
 * CLOCKING BLOCKS:
 * 
 * PURPOSE:
 * - Provide synchronous, race-free signal access
 * - Define input/output skew for sampling/driving
 * - Simplify testbench synchronization
 * - Enable cycle-based delays with ##
 * 
 * SYNTAX:
 * clocking cb @(posedge clk);
 *     default input #1ns output #1ns;
 *     input signal1;
 *     output signal2;
 * endclocking
 * 
 * INPUT SKEW:
 * input #1ns signal;
 * - Sample signal 1ns after clock edge
 * - Avoids race with DUT output
 * - Ensures stable value
 * 
 * OUTPUT SKEW:
 * output #1ns signal;
 * - Drive signal 1ns after clock edge
 * - Default #0 drives before clock
 * - Timing control
 * 
 * DEFAULT SKEWS:
 * default input #1ns output #1ns;
 * - Applies to all signals without explicit skew
 * - Can be overridden per signal
 * 
 * CYCLE DELAYS:
 * ##N  - Wait N clock cycles
 * ##1  - Wait 1 cycle
 * ##5  - Wait 5 cycles
 * 
 * Equivalent to:
 * repeat(N) @(clocking_block);
 * 
 * ACCESSING SIGNALS:
 * - Direct: vif.cb.signal
 * - Wait on edge: @(vif.cb);
 * - Cycle delay: ##N;
 * 
 * BENEFITS:
 * 1. Race-free: Input skew avoids races
 * 2. Cleaner code: ##N instead of repeat()@()
 * 3. Synchronous: All accesses synchronized
 * 4. Safe sampling: Consistent timing
 * 5. Intent clear: Input/output roles explicit
 * 
 * COMMON PATTERNS:
 * 
 * 1. Driver Pattern:
 * @(vif.cb);
 * vif.cb.addr <= addr_value;
 * vif.cb.data <= data_value;
 * 
 * 2. Wait Pattern:
 * @(vif.cb);
 * while (!vif.cb.ready)
 *     @(vif.cb);
 * 
 * 3. Sample Pattern:
 * @(vif.cb);
 * captured_data = vif.cb.data;
 * 
 * 4. Delay Pattern:
 * ##5;  // Wait 5 cycles
 * 
 * BEST PRACTICES:
 * 1. Always use in testbench, not DUT
 * 2. Use input skew (e.g., #1ns) to avoid races
 * 3. Output skew #0 for setup time
 * 4. One clocking block per role (master, slave, monitor)
 * 5. Include in modports
 * 6. Use ## for cycle delays
 * 
 * WITH MODPORTS:
 * modport master (
 *     clocking master_cb,
 *     input rst_n
 * );
 * 
 * Usage:
 * @(vif.master_cb);
 * vif.master_cb.signal <= value;
 * 
 * VERSUS RAW SIGNALS:
 * 
 * Without clocking block (races possible):
 * @(posedge clk);
 * data = vif.data;  // May sample during transition!
 * 
 * With clocking block (race-free):
 * @(vif.cb);
 * data = vif.cb.data;  // Samples at safe time
 * 
 * TIMING DIAGRAM:
 * 
 * CLK:    ___/‾‾‾\___/‾‾‾\___
 * 
 * DUT output:  ====[X]====[Y]====
 * 
 * Sample (no skew):   ↑ (race!)
 * Sample (1ns skew):     ↑ (safe)
 * 
 * MULTIPLE CLOCK DOMAINS:
 * - Create separate clocking blocks per clock
 * - Each synchronized to different clock
 * - CDC verification
 * 
 * ASSERTIONS WITH CLOCKING BLOCKS:
 * property p;
 *     @(cb) signal1 |-> ##1 signal2;
 * endproperty
 * 
 * - Samples at clocking block edges
 * - Race-free checking
 * - Clean specification
 * 
 * COMMON MISTAKES:
 * ❌ No input skew (races)
 * ❌ Using in DUT (only for TB)
 * ❌ Wrong clock edge
 * ❌ Mixing raw and clocked access
 * ✅ Always use input skew (#1ns)
 * ✅ Only in testbench
 * ✅ Consistent clock edge
 * ✅ All TB access through clocking block
 */
