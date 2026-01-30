// ============================================================================
// modport_usage.sv - Modport Usage and Best Practices
// ============================================================================

// ============================================================================
// Basic Modport Example
// ============================================================================
interface basic_if(input logic clk);
    logic [7:0] data;
    logic valid;
    logic ready;
    
    // Producer modport (drives data/valid, samples ready)
    modport producer (
        input  clk,
        output data,
        output valid,
        input  ready
    );
    
    // Consumer modport (samples data/valid, drives ready)
    modport consumer (
        input  clk,
        input  data,
        input  valid,
        output ready
    );
    
    // Monitor modport (samples everything)
    modport monitor (
        input clk,
        input data,
        input valid,
        input ready
    );
endinterface

// ============================================================================
// Modports with Clocking Blocks
// ============================================================================
interface synch_if(input logic clk, input logic rst_n);
    logic [31:0] addr;
    logic [31:0] data;
    logic req;
    logic ack;
    
    // Master clocking block
    clocking master_cb @(posedge clk);
        default input #1ns output #1ns;
        output addr, data, req;
        input ack;
    endclocking
    
    // Slave clocking block
    clocking slave_cb @(posedge clk);
        default input #1ns output #1ns;
        input addr, data, req;
        output ack;
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
endinterface

// ============================================================================
// Modports with Methods
// ============================================================================
interface method_if(input logic clk);
    logic [15:0] addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic we, re;
    
    // Write task
    task automatic do_write(input logic [15:0] a, input logic [31:0] d);
        @(posedge clk);
        addr <= a;
        wdata <= d;
        we <= 1'b1;
        re <= 1'b0;
        @(posedge clk);
        we <= 1'b0;
    endtask
    
    // Read task
    task automatic do_read(input logic [15:0] a, output logic [31:0] d);
        @(posedge clk);
        addr <= a;
        re <= 1'b1;
        we <= 1'b0;
        @(posedge clk);
        d = rdata;
        re <= 1'b0;
    endtask
    
    // Master modport with methods
    modport master (
        input  clk,
        output addr, wdata, we, re,
        input  rdata,
        import do_write, do_read
    );
    
    // Slave modport (no methods needed)
    modport slave (
        input clk, addr, wdata, we, re,
        output rdata
    );
endinterface

// ============================================================================
// Bidirectional Modports
// ============================================================================
interface bidir_if(input logic clk);
    logic [7:0] data;
    logic dir;  // 0=input, 1=output
    
    // Agent A perspective
    modport agent_a (
        input  clk,
        inout  data,
        output dir
    );
    
    // Agent B perspective
    modport agent_b (
        input  clk,
        inout  data,
        input  dir
    );
endinterface

// ============================================================================
// Hierarchical Modports
// ============================================================================
interface hierarchical_if(input logic clk, input logic rst_n);
    logic [31:0] control;
    logic [31:0] status;
    logic [31:0] data;
    
    // Control-only modport
    modport controller (
        input  clk, rst_n,
        output control,
        input  status
    );
    
    // Data-only modport
    modport datapath (
        input  clk, rst_n,
        input  control,
        output status,
        inout  data
    );
    
    // Full access modport
    modport full (
        input clk, rst_n,
        output control,
        input status,
        inout data
    );
    
    // Monitor modport (read-only)
    modport monitor (
        input clk, rst_n, control, status, data
    );
endinterface

// ============================================================================
// Modports with Exports (for nested modules)
// ============================================================================
interface master_slave_if(input logic clk);
    logic [31:0] mosi_data;  // Master out, slave in
    logic [31:0] miso_data;  // Master in, slave out
    logic valid;
    logic ready;
    
    modport master (
        input  clk,
        output mosi_data,
        input  miso_data,
        output valid,
        input  ready
    );
    
    modport slave (
        input  clk,
        input  mosi_data,
        output miso_data,
        input  valid,
        output ready
    );
    
    // Can export modports for hierarchical connections
    modport master_export (
        export master
    );
    
    modport slave_export (
        export slave
    );
endinterface

// ============================================================================
// Example Modules Using Modports
// ============================================================================

// Producer module
module producer (
    basic_if.producer bus
);
    always_ff @(posedge bus.clk) begin
        if (bus.ready) begin
            bus.data <= $urandom;
            bus.valid <= 1'b1;
        end else begin
            bus.valid <= 1'b0;
        end
    end
endmodule

// Consumer module
module consumer (
    basic_if.consumer bus
);
    always_ff @(posedge bus.clk) begin
        bus.ready <= $urandom_range(0, 1);
        
        if (bus.valid && bus.ready) begin
            $display("[CONSUMER] Received: 0x%h", bus.data);
        end
    end
endmodule

// Monitor module
module monitor (
    basic_if.monitor bus
);
    always_ff @(posedge bus.clk) begin
        if (bus.valid && bus.ready) begin
            $display("[MONITOR] Transaction: data=0x%h", bus.data);
        end
    end
endmodule

// Master using methods
class master_driver;
    virtual method_if.master bus;
    
    function new(virtual method_if.master b);
        bus = b;
    endfunction
    
    task run();
        logic [31:0] rd_data;
        
        // Use imported methods
        bus.do_write(16'h100, 32'hDEADBEEF);
        $display("[MASTER] Wrote 0xDEADBEEF to 0x100");
        
        bus.do_read(16'h100, rd_data);
        $display("[MASTER] Read 0x%h from 0x100", rd_data);
    endtask
endclass

// ============================================================================
// Real-World Example: APB Interface with Modports
// ============================================================================
interface apb_if(input logic clk, input logic rst_n);
    logic [31:0] paddr;
    logic        psel;
    logic        penable;
    logic        pwrite;
    logic [31:0] pwdata;
    logic [31:0] prdata;
    logic        pready;
    logic        pslverr;
    
    // Master modport
    modport master (
        input  clk, rst_n,
        output paddr,
        output psel,
        output penable,
        output pwrite,
        output pwdata,
        input  prdata,
        input  pready,
        input  pslverr
    );
    
    // Slave modport
    modport slave (
        input  clk, rst_n,
        input  paddr,
        input  psel,
        input  penable,
        input  pwrite,
        input  pwdata,
        output prdata,
        output pready,
        output pslverr
    );
    
    // Monitor modport (passive observation)
    modport monitor (
        input clk, rst_n,
        input paddr, psel, penable, pwrite,
        input pwdata, prdata, pready, pslverr
    );
    
    // Assertions modport (for verification)
    modport assertions (
        input clk, rst_n,
        input paddr, psel, penable, pwrite,
        input pwdata, prdata, pready, pslverr
    );
    
    // Protocol checker
    property setup_to_access;
        @(posedge clk) disable iff (!rst_n)
        (psel && !penable) |=> (psel && penable);
    endproperty
    
    assert property (setup_to_access)
        else $error("APB protocol violation: setup not followed by access");
endinterface

// ============================================================================
// Testbench Demonstrating Modport Usage
// ============================================================================
module modport_usage;
    logic clk, rst_n;
    
    // Interfaces
    basic_if basic(clk);
    method_if method(clk);
    apb_if apb(clk, rst_n);
    
    // Modules connected via modports
    producer prod(.bus(basic.producer));
    consumer cons(.bus(basic.consumer));
    monitor mon(.bus(basic.monitor));
    
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
    
    // Test using master with methods
    initial begin
        master_driver mst;
        
        @(posedge rst_n);
        repeat(5) @(posedge clk);
        
        $display("\n=== Modport with Methods Test ===");
        mst = new(method.master);
        mst.run();
        
        #1000;
        $finish;
    end
    
    // Waveform dump
    initial begin
        $dumpfile("modport_usage.vcd");
        $dumpvars(0, modport_usage);
    end
    
endmodule

/*
 * MODPORT USAGE GUIDE:
 * 
 * WHAT ARE MODPORTS?
 * - Module ports for interfaces
 * - Define signal direction from module's perspective
 * - Restrict what module can access
 * - Enable connection checking at compile time
 * 
 * WHY USE MODPORTS?
 * 1. Clarity: Clear master/slave/monitor roles
 * 2. Safety: Prevents accidental writes to inputs
 * 3. Documentation: Self-documenting interfaces
 * 4. Reuse: Same interface, different perspectives
 * 5. Verification: Compile-time checking
 * 
 * COMMON MODPORT PATTERNS:
 * 
 * 1. Master/Slave:
 *    modport master (output req, input ack);
 *    modport slave (input req, output ack);
 * 
 * 2. Producer/Consumer:
 *    modport producer (output data, valid, input ready);
 *    modport consumer (input data, valid, output ready);
 * 
 * 3. Monitor (passive):
 *    modport monitor (input clk, data, valid, ready);
 * 
 * 4. Driver/Receiver:
 *    modport driver (clocking driver_cb);
 *    modport receiver (clocking receiver_cb);
 * 
 * MODPORT FEATURES:
 * - Signal direction (input, output, inout, ref)
 * - Clocking blocks
 * - Imported methods (tasks/functions)
 * - Exported modports (hierarchical)
 * 
 * WITH CLOCKING BLOCKS:
 * modport master (
 *     clocking master_cb,
 *     input rst_n
 * );
 * 
 * Benefits:
 * - Synchronous access
 * - Race-free driving/sampling
 * - Input/output skew
 * 
 * WITH METHODS:
 * interface my_if;
 *     task do_transfer(...);
 *     endtask
 *     
 *     modport master (
 *         import do_transfer
 *     );
 * endinterface
 * 
 * Benefits:
 * - Protocol encapsulation
 * - Reusable operations
 * - Hide timing details
 * 
 * BEST PRACTICES:
 * 1. Always use modports (never connect raw interface)
 * 2. Name modports after their role (master, slave, monitor)
 * 3. Monitor modports should be input-only
 * 4. Use clocking blocks with modports for TB
 * 5. Import methods that belong to that role
 * 6. Document each modport's purpose
 * 
 * VERIFICATION USAGE:
 * - Driver: Use master/driver modport
 * - Monitor: Use monitor modport (all inputs)
 * - DUT: Use slave/device modport
 * - BFM: Use modports with methods
 * 
 * COMPILE-TIME CHECKS:
 * - Can't write to input
 * - Can't read undriven output
 * - Direction mismatch detected
 * - Missing signals caught
 * 
 * ADVANTAGES:
 * + Clearer intent
 * + Better encapsulation
 * + Compile-time safety
 * + Easier maintenance
 * + Self-documenting
 * 
 * WITHOUT MODPORTS:
 * module my_module(my_if bus);
 *   // Can access everything - dangerous!
 *   // No compile-time checking
 *   // Unclear what should be inputs/outputs
 * endmodule
 * 
 * WITH MODPORTS:
 * module my_module(my_if.master bus);
 *   // Can only access what master can
 *   // Compile-time direction checking
 *   // Clear role and intent
 * endmodule
 * 
 * COMMON MISTAKES TO AVOID:
 * ❌ Connecting without modport
 * ❌ Using wrong modport for role
 * ❌ Making monitor modport output signals
 * ❌ Not using clocking blocks in TB
 * ✅ Always specify modport
 * ✅ Use appropriate modport for each component
 * ✅ Monitor modports are input-only
 * ✅ Use clocking blocks for synchronous access
 */
