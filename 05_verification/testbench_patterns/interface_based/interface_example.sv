// ============================================================================
// interface_example.sv - SystemVerilog Interface Examples
// ============================================================================

// ============================================================================
// Basic Interface
// ============================================================================
interface simple_bus_if(input logic clk);
    logic [7:0] addr;
    logic [31:0] data;
    logic valid;
    logic ready;
endinterface

// ============================================================================
// Interface with Modports
// ============================================================================
interface bus_if(input logic clk);
    logic [15:0] addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic we;
    logic re;
    logic ready;
    
    // Master perspective
    modport master (
        input  clk,
        output addr,
        output wdata,
        input  rdata,
        output we,
        output re,
        input  ready
    );
    
    // Slave perspective
    modport slave (
        input  clk,
        input  addr,
        input  wdata,
        output rdata,
        input  we,
        input  re,
        output ready
    );
    
    // Monitor perspective (all inputs)
    modport monitor (
        input clk,
        input addr,
        input wdata,
        input rdata,
        input we,
        input re,
        input ready
    );
endinterface

// ============================================================================
// Interface with Clocking Blocks
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
    
    // Master clocking block
    clocking master_cb @(posedge clk);
        default input #1ns output #1ns;
        output paddr;
        output psel;
        output penable;
        output pwrite;
        output pwdata;
        input  prdata;
        input  pready;
        input  pslverr;
    endclocking
    
    // Slave clocking block
    clocking slave_cb @(posedge clk);
        default input #1ns output #1ns;
        input  paddr;
        input  psel;
        input  penable;
        input  pwrite;
        input  pwdata;
        output prdata;
        output pready;
        output pslverr;
    endclocking
    
    // Monitor clocking block
    clocking monitor_cb @(posedge clk);
        default input #1ns;
        input paddr;
        input psel;
        input penable;
        input pwrite;
        input pwdata;
        input prdata;
        input pready;
        input pslverr;
    endclocking
    
    // Modports with clocking blocks
    modport master (clocking master_cb, input rst_n);
    modport slave (clocking slave_cb, input rst_n);
    modport monitor (clocking monitor_cb, input rst_n);
    
    // Reset synchronization task
    task wait_reset_done();
        wait(rst_n == 0);
        wait(rst_n == 1);
        @(posedge clk);
    endtask
    
endinterface

// ============================================================================
// Interface with Methods (Tasks and Functions)
// ============================================================================
interface axi_lite_if(input logic clk, input logic rst_n);
    // Signals
    logic [31:0] awaddr;
    logic        awvalid;
    logic        awready;
    
    logic [31:0] wdata;
    logic [3:0]  wstrb;
    logic        wvalid;
    logic        wready;
    
    logic [1:0]  bresp;
    logic        bvalid;
    logic        bready;
    
    logic [31:0] araddr;
    logic        arvalid;
    logic        arready;
    
    logic [31:0] rdata;
    logic [1:0]  rresp;
    logic        rvalid;
    logic        rready;
    
    // Write transaction task
    task automatic write(input logic [31:0] addr, 
                        input logic [31:0] data,
                        input logic [3:0] strb = 4'hF);
        // Address phase
        @(posedge clk);
        awaddr <= addr;
        awvalid <= 1'b1;
        wdata <= data;
        wstrb <= strb;
        wvalid <= 1'b1;
        
        // Wait for address acceptance
        do @(posedge clk);
        while (!awready);
        awvalid <= 1'b0;
        
        // Wait for data acceptance
        while (!wready) @(posedge clk);
        wvalid <= 1'b0;
        
        // Wait for response
        bready <= 1'b1;
        while (!bvalid) @(posedge clk);
        @(posedge clk);
        bready <= 1'b0;
    endtask
    
    // Read transaction task
    task automatic read(input logic [31:0] addr, 
                       output logic [31:0] data);
        // Address phase
        @(posedge clk);
        araddr <= addr;
        arvalid <= 1'b1;
        
        // Wait for address acceptance
        do @(posedge clk);
        while (!arready);
        arvalid <= 1'b0;
        
        // Wait for data
        rready <= 1'b1;
        while (!rvalid) @(posedge clk);
        data = rdata;
        @(posedge clk);
        rready <= 1'b0;
    endtask
    
    // Reset task
    task automatic reset_master();
        awaddr <= 32'h0;
        awvalid <= 1'b0;
        wdata <= 32'h0;
        wstrb <= 4'h0;
        wvalid <= 1'b0;
        bready <= 1'b0;
        araddr <= 32'h0;
        arvalid <= 1'b0;
        rready <= 1'b0;
    endtask
    
    // Modport
    modport master (
        input clk, rst_n,
        output awaddr, awvalid, input awready,
        output wdata, wstrb, wvalid, input wready,
        input bresp, bvalid, output bready,
        output araddr, arvalid, input arready,
        input rdata, rresp, rvalid, output rready,
        import write, read, reset_master
    );
    
endinterface

// ============================================================================
// Interface with Parameters
// ============================================================================
interface param_bus_if #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic [ADDR_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] wdata;
    logic [DATA_WIDTH-1:0] rdata;
    logic we;
    logic re;
    logic valid;
    
    modport master (
        input  clk, rst_n,
        output addr, wdata, we, re,
        input  rdata, valid
    );
    
    modport slave (
        input  clk, rst_n,
        input  addr, wdata, we, re,
        output rdata, valid
    );
endinterface

// ============================================================================
// Interface with Assertions
// ============================================================================
interface checked_bus_if(input logic clk, input logic rst_n);
    logic [31:0] addr;
    logic [31:0] data;
    logic valid;
    logic ready;
    
    // Protocol assertions
    property valid_requires_ready;
        @(posedge clk) disable iff (!rst_n)
        valid |-> ##[0:10] ready;
    endproperty
    
    property no_change_until_ready;
        @(posedge clk) disable iff (!rst_n)
        (valid && !ready) |=> $stable(addr) && $stable(data);
    endproperty
    
    assert property (valid_requires_ready)
        else $error("Valid asserted but no ready within 10 cycles");
    
    assert property (no_change_until_ready)
        else $error("Addr/data changed before ready");
    
    // Coverage
    covergroup cg @(posedge clk);
        cp_valid: coverpoint valid;
        cp_ready: coverpoint ready;
        cross_valid_ready: cross valid, ready;
    endgroup
    
    cg cg_inst = new();
    
endinterface

// ============================================================================
// Hierarchical Interface (Nested)
// ============================================================================
interface clock_if;
    logic clk;
    logic rst_n;
    
    task wait_cycles(int n);
        repeat(n) @(posedge clk);
    endtask
endinterface

interface data_if;
    logic [31:0] data;
    logic valid;
    
    function automatic bit is_valid();
        return valid;
    endfunction
endinterface

interface system_if;
    clock_if clk_if();
    data_if  data_if();
    
    // Can access nested interfaces
    task wait_for_valid_data();
        while (!data_if.is_valid())
            clk_if.wait_cycles(1);
    endtask
endinterface

// ============================================================================
// Simple DUT for demonstration
// ============================================================================
module simple_slave (
    bus_if.slave bus
);
    logic [31:0] memory [256];
    
    always_ff @(posedge bus.clk) begin
        bus.ready <= 1'b0;
        
        if (bus.we) begin
            memory[bus.addr[7:0]] <= bus.wdata;
            bus.ready <= 1'b1;
        end
        
        if (bus.re) begin
            bus.rdata <= memory[bus.addr[7:0]];
            bus.ready <= 1'b1;
        end
    end
endmodule

// ============================================================================
// Testbench
// ============================================================================
module interface_example;
    logic clk, rst_n;
    
    // Instantiate interfaces
    bus_if bus(clk);
    apb_if apb(clk, rst_n);
    axi_lite_if axi(clk, rst_n);
    checked_bus_if checked(clk, rst_n);
    
    // DUT
    simple_slave dut(.bus(bus.slave));
    
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
    
    // Test using bus interface
    initial begin
        // Wait for reset
        @(posedge rst_n);
        @(posedge clk);
        
        $display("=== Bus Interface Test ===");
        
        // Write using master modport
        bus.master.we <= 1'b1;
        bus.master.addr <= 16'h10;
        bus.master.wdata <= 32'hDEADBEEF;
        @(posedge clk);
        while (!bus.master.ready) @(posedge clk);
        bus.master.we <= 1'b0;
        $display("Wrote 0x%h to addr 0x%h", 32'hDEADBEEF, 16'h10);
        
        // Read back
        @(posedge clk);
        bus.master.re <= 1'b1;
        bus.master.addr <= 16'h10;
        @(posedge clk);
        while (!bus.master.ready) @(posedge clk);
        $display("Read 0x%h from addr 0x%h", bus.master.rdata, 16'h10);
        bus.master.re <= 1'b0;
        
        #100;
    end
    
    // Test using AXI interface with methods
    initial begin
        logic [31:0] read_data;
        
        @(posedge rst_n);
        axi.reset_master();
        repeat(5) @(posedge clk);
        
        $display("\n=== AXI Interface Test (with methods) ===");
        
        // Use built-in write task
        axi.write(32'h1000, 32'hCAFEBABE, 4'hF);
        $display("AXI Write: addr=0x1000, data=0xCAFEBABE");
        
        // Use built-in read task
        axi.read(32'h2000, read_data);
        $display("AXI Read: addr=0x2000, data=0x%h", read_data);
        
        #100;
    end
    
    // Test checked interface
    initial begin
        @(posedge rst_n);
        repeat(5) @(posedge clk);
        
        $display("\n=== Checked Interface Test ===");
        
        // Valid handshake
        checked.valid <= 1'b1;
        checked.addr <= 32'h5000;
        checked.data <= 32'h12345678;
        
        repeat(3) @(posedge clk);
        checked.ready <= 1'b1;
        @(posedge clk);
        checked.valid <= 1'b0;
        checked.ready <= 1'b0;
        
        $display("Protocol assertions checked");
        
        #100;
        $finish;
    end
    
    // Waveform dump
    initial begin
        $dumpfile("interface_example.vcd");
        $dumpvars(0, interface_example);
    end
    
endmodule

/*
 * SYSTEMVERILOG INTERFACES:
 * 
 * BENEFITS:
 * 1. Bundle related signals together
 * 2. Simplify port connections
 * 3. Modports for different perspectives
 * 4. Clocking blocks for synchronization
 * 5. Tasks/functions for protocol encapsulation
 * 6. Assertions for protocol checking
 * 7. Reusability across projects
 * 
 * MODPORTS:
 * - Define signal directions for different roles
 * - Master vs Slave perspectives
 * - Monitor (all inputs)
 * - Reduces connection errors
 * 
 * CLOCKING BLOCKS:
 * - Synchronous sampling/driving
 * - Input/output skew control
 * - Race condition avoidance
 * - Testbench synchronization
 * 
 * METHODS (Tasks/Functions):
 * - Encapsulate protocol transactions
 * - Reusable across tests
 * - Hide timing details
 * - Simplify test code
 * 
 * PARAMETERS:
 * - Configurable width
 * - Reusable across designs
 * - Compile-time customization
 * 
 * ASSERTIONS IN INTERFACES:
 * - Protocol checking
 * - Formal verification
 * - Runtime verification
 * - Self-documenting
 * 
 * BEST PRACTICES:
 * 1. Use modports for clarity
 * 2. Add clocking blocks for testbench
 * 3. Include protocol tasks
 * 4. Add assertions for checking
 * 5. Document interface protocol
 * 6. Use parameters for flexibility
 * 7. Group related signals
 * 
 * COMMON PATTERNS:
 * - Bus protocols (AXI, APB, AHB)
 * - Streaming interfaces
 * - Memory interfaces
 * - Custom protocols
 * 
 * vs BUNDLES OF WIRES:
 * Interfaces:
 * + Clean connections
 * + Protocol encapsulation
 * + Easier maintenance
 * + Better abstraction
 * 
 * Wire bundles:
 * - Error-prone connections
 * - No protocol checking
 * - Hard to maintain
 * - Low-level
 */
