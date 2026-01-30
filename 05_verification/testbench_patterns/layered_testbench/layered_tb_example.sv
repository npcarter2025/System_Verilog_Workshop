// ============================================================================
// layered_tb_example.sv - Complete Layered Testbench Architecture
// ============================================================================
// This example demonstrates a full layered testbench architecture without UVM,
// showing the fundamental concepts that UVM builds upon.
// ============================================================================

// ============================================================================
// DUT: Simple FIFO for demonstration
// ============================================================================
module fifo_dut #(
    parameter WIDTH = 8,
    parameter DEPTH = 16
) (
    input  logic clk,
    input  logic rst_n,
    
    // Write interface
    input  logic wr_en,
    input  logic [WIDTH-1:0] wr_data,
    output logic full,
    
    // Read interface
    input  logic rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic empty,
    
    // Status
    output logic [$clog2(DEPTH):0] count
);
    logic [WIDTH-1:0] mem [0:DEPTH-1];
    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
            count <= 0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr] <= wr_data;
                wr_ptr <= wr_ptr + 1;
                count <= count + 1;
            end
            
            if (rd_en && !empty) begin
                rd_ptr <= rd_ptr + 1;
                count <= count - 1;
            end
            
            if (wr_en && !full && rd_en && !empty) begin
                count <= count;  // Both ops cancel out
            end
        end
    end
    
    assign rd_data = mem[rd_ptr];
    assign full = (count == DEPTH);
    assign empty = (count == 0);
    
endmodule

// ============================================================================
// LAYER 1: Transaction (Data Structure)
// ============================================================================
class fifo_transaction;
    // Transaction fields
    rand bit [7:0] data;
    rand bit is_write;
    time timestamp;
    
    // Constraints
    constraint valid_c {
        data inside {[0:255]};
    }
    
    // Constructor
    function new();
        timestamp = $time;
    endfunction
    
    // Copy function
    function fifo_transaction copy();
        fifo_transaction tr = new();
        tr.data = this.data;
        tr.is_write = this.is_write;
        tr.timestamp = this.timestamp;
        return tr;
    endfunction
    
    // Compare function
    function bit compare(fifo_transaction tr);
        return (this.data == tr.data);
    endfunction
    
    // Display function
    function void display(string prefix = "");
        $display("%s [%0t] %s: data=0x%0h", 
                prefix, timestamp, is_write ? "WRITE" : "READ", data);
    endfunction
endclass

// ============================================================================
// LAYER 2: Driver (Converts transactions to pin wiggles)
// ============================================================================
class fifo_driver;
    virtual fifo_if vif;
    mailbox #(fifo_transaction) gen2drv;
    int num_transactions;
    
    function new(virtual fifo_if vif, mailbox #(fifo_transaction) gen2drv);
        this.vif = vif;
        this.gen2drv = gen2drv;
        this.num_transactions = 0;
    endfunction
    
    task run();
        fifo_transaction tr;
        
        $display("[DRIVER] Starting...");
        
        forever begin
            gen2drv.get(tr);
            drive_transaction(tr);
            num_transactions++;
        end
    endtask
    
    task drive_transaction(fifo_transaction tr);
        if (tr.is_write) begin
            // Drive write transaction
            @(posedge vif.clk);
            vif.wr_en <= 1'b1;
            vif.wr_data <= tr.data;
            vif.rd_en <= 1'b0;
            @(posedge vif.clk);
            vif.wr_en <= 1'b0;
            $display("[DRIVER] Wrote 0x%0h", tr.data);
        end else begin
            // Drive read transaction
            @(posedge vif.clk);
            vif.rd_en <= 1'b1;
            vif.wr_en <= 1'b0;
            @(posedge vif.clk);
            vif.rd_en <= 1'b0;
            $display("[DRIVER] Read request");
        end
    endtask
    
    task reset();
        vif.wr_en <= 1'b0;
        vif.rd_en <= 1'b0;
        vif.wr_data <= 8'h0;
    endtask
endclass

// ============================================================================
// LAYER 3: Monitor (Observes pin activity and creates transactions)
// ============================================================================
class fifo_monitor;
    virtual fifo_if vif;
    mailbox #(fifo_transaction) mon2scb;
    int num_transactions;
    
    function new(virtual fifo_if vif, mailbox #(fifo_transaction) mon2scb);
        this.vif = vif;
        this.mon2scb = mon2scb;
        this.num_transactions = 0;
    endfunction
    
    task run();
        fifo_transaction tr;
        
        $display("[MONITOR] Starting...");
        
        forever begin
            @(posedge vif.clk);
            
            // Monitor writes
            if (vif.wr_en && !vif.full) begin
                tr = new();
                tr.is_write = 1;
                tr.data = vif.wr_data;
                tr.timestamp = $time;
                mon2scb.put(tr);
                $display("[MONITOR] Captured write: 0x%0h", tr.data);
                num_transactions++;
            end
            
            // Monitor reads
            if (vif.rd_en && !vif.empty) begin
                @(posedge vif.clk);  // Get data next cycle
                tr = new();
                tr.is_write = 0;
                tr.data = vif.rd_data;
                tr.timestamp = $time;
                mon2scb.put(tr);
                $display("[MONITOR] Captured read: 0x%0h", tr.data);
                num_transactions++;
            end
        end
    endtask
endclass

// ============================================================================
// LAYER 4: Generator (Creates random/directed transactions)
// ============================================================================
class fifo_generator;
    mailbox #(fifo_transaction) gen2drv;
    int num_transactions;
    event gen_done;
    
    function new(mailbox #(fifo_transaction) gen2drv);
        this.gen2drv = gen2drv;
        this.num_transactions = 0;
    endfunction
    
    task run(int count);
        fifo_transaction tr;
        
        $display("[GENERATOR] Starting, generating %0d transactions", count);
        
        repeat(count) begin
            tr = new();
            assert(tr.randomize());
            gen2drv.put(tr);
            num_transactions++;
            #10;
        end
        
        -> gen_done;
        $display("[GENERATOR] Completed %0d transactions", num_transactions);
    endtask
    
    task directed_sequence();
        fifo_transaction tr;
        
        $display("[GENERATOR] Running directed sequence");
        
        // Fill FIFO
        repeat(20) begin
            tr = new();
            tr.is_write = 1;
            assert(tr.randomize());
            gen2drv.put(tr);
        end
        
        // Drain FIFO
        repeat(20) begin
            tr = new();
            tr.is_write = 0;
            gen2drv.put(tr);
        end
        
        -> gen_done;
    endtask
endclass

// ============================================================================
// LAYER 5: Scoreboard (Checks correctness)
// ============================================================================
class fifo_scoreboard;
    mailbox #(fifo_transaction) mon2scb;
    bit [7:0] expected_queue[$];
    int num_matches;
    int num_mismatches;
    
    function new(mailbox #(fifo_transaction) mon2scb);
        this.mon2scb = mon2scb;
        this.num_matches = 0;
        this.num_mismatches = 0;
    endfunction
    
    task run();
        fifo_transaction tr;
        
        $display("[SCOREBOARD] Starting...");
        
        forever begin
            mon2scb.get(tr);
            check_transaction(tr);
        end
    endtask
    
    task check_transaction(fifo_transaction tr);
        if (tr.is_write) begin
            // Write: add to expected queue
            expected_queue.push_back(tr.data);
            $display("[SCOREBOARD] Queued write: 0x%0h (queue size: %0d)", 
                    tr.data, expected_queue.size());
        end else begin
            // Read: check against expected queue
            if (expected_queue.size() == 0) begin
                $display("[SCOREBOARD] ERROR: Read from empty FIFO!");
                num_mismatches++;
            end else begin
                bit [7:0] expected = expected_queue.pop_front();
                if (tr.data == expected) begin
                    $display("[SCOREBOARD] PASS: Read 0x%0h (expected 0x%0h)", 
                            tr.data, expected);
                    num_matches++;
                end else begin
                    $display("[SCOREBOARD] FAIL: Read 0x%0h (expected 0x%0h)", 
                            tr.data, expected);
                    num_mismatches++;
                end
            end
        end
    endtask
    
    function void report();
        $display("\n=== SCOREBOARD REPORT ===");
        $display("Matches:    %0d", num_matches);
        $display("Mismatches: %0d", num_mismatches);
        $display("Queue size: %0d", expected_queue.size());
        if (num_mismatches == 0 && expected_queue.size() == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
    endfunction
endclass

// ============================================================================
// LAYER 6: Coverage (Functional coverage collector)
// ============================================================================
class fifo_coverage;
    fifo_transaction tr_stream[$];
    
    covergroup cg;
        cp_data: coverpoint tr_stream[$].data {
            bins low = {[0:63]};
            bins mid = {[64:191]};
            bins high = {[192:255]};
        }
        
        cp_operation: coverpoint tr_stream[$].is_write {
            bins write = {1};
            bins read = {0};
        }
    endgroup
    
    function new();
        cg = new();
    endfunction
    
    function void sample(fifo_transaction tr);
        tr_stream.push_back(tr);
        cg.sample();
    endfunction
    
    function void report();
        $display("\n=== COVERAGE REPORT ===");
        $display("Overall coverage: %0.2f%%", cg.get_coverage());
    endfunction
endclass

// ============================================================================
// LAYER 7: Environment (Connects all components)
// ============================================================================
class fifo_environment;
    virtual fifo_if vif;
    
    fifo_generator gen;
    fifo_driver drv;
    fifo_monitor mon;
    fifo_scoreboard scb;
    fifo_coverage cov;
    
    mailbox #(fifo_transaction) gen2drv;
    mailbox #(fifo_transaction) mon2scb;
    
    function new(virtual fifo_if vif);
        this.vif = vif;
        
        // Create mailboxes
        gen2drv = new();
        mon2scb = new();
        
        // Create components
        gen = new(gen2drv);
        drv = new(vif, gen2drv);
        mon = new(vif, mon2scb);
        scb = new(mon2scb);
        cov = new();
        
        $display("[ENVIRONMENT] Created");
    endfunction
    
    task build();
        $display("[ENVIRONMENT] Building...");
    endtask
    
    task reset();
        $display("[ENVIRONMENT] Resetting DUT...");
        vif.rst_n = 0;
        drv.reset();
        repeat(5) @(posedge vif.clk);
        vif.rst_n = 1;
        repeat(5) @(posedge vif.clk);
        $display("[ENVIRONMENT] Reset complete");
    endtask
    
    task run();
        $display("[ENVIRONMENT] Starting all components...");
        
        fork
            drv.run();
            mon.run();
            scb.run();
        join_none
    endtask
    
    task wait_for_end();
        @(gen.gen_done);
        #1000;  // Let transactions drain
    endtask
    
    function void report();
        $display("\n" );
        $display("======================================");
        $display("       FINAL TEST REPORT");
        $display("======================================");
        $display("Generator:  %0d transactions", gen.num_transactions);
        $display("Driver:     %0d transactions", drv.num_transactions);
        $display("Monitor:    %0d transactions", mon.num_transactions);
        scb.report();
        cov.report();
        $display("======================================\n");
    endfunction
endclass

// ============================================================================
// LAYER 8: Test (Top-level test scenario)
// ============================================================================
class fifo_test;
    fifo_environment env;
    
    function new(virtual fifo_if vif);
        env = new(vif);
    endfunction
    
    task run();
        $display("\n");
        $display("======================================");
        $display("       STARTING FIFO TEST");
        $display("======================================\n");
        
        env.build();
        env.reset();
        env.run();
        
        // Run test stimulus
        env.gen.run(50);
        
        env.wait_for_end();
        env.report();
        
        $display("\n");
        $display("======================================");
        $display("       TEST COMPLETED");
        $display("======================================\n");
    endtask
endclass

// ============================================================================
// Interface
// ============================================================================
interface fifo_if(input logic clk);
    logic rst_n;
    logic wr_en;
    logic [7:0] wr_data;
    logic full;
    logic rd_en;
    logic [7:0] rd_data;
    logic empty;
    logic [4:0] count;
endinterface

// ============================================================================
// Top-Level Module
// ============================================================================
module layered_tb_example;
    logic clk;
    
    // Interface
    fifo_if fif(clk);
    
    // DUT
    fifo_dut #(
        .WIDTH(8),
        .DEPTH(16)
    ) dut (
        .clk(clk),
        .rst_n(fif.rst_n),
        .wr_en(fif.wr_en),
        .wr_data(fif.wr_data),
        .full(fif.full),
        .rd_en(fif.rd_en),
        .rd_data(fif.rd_data),
        .empty(fif.empty),
        .count(fif.count)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Test execution
    initial begin
        fifo_test test;
        test = new(fif);
        test.run();
        #100;
        $finish;
    end
    
    // Waveform dump
    initial begin
        $dumpfile("layered_tb.vcd");
        $dumpvars(0, layered_tb_example);
    end
    
    // Timeout
    initial begin
        #100000;
        $display("ERROR: Test timeout!");
        $finish;
    end
    
endmodule

/*
 * LAYERED TESTBENCH ARCHITECTURE:
 * 
 * LAYER HIERARCHY (Bottom to Top):
 * 
 * Layer 1: Transaction
 *   - Data structure representing a stimulus/response
 *   - Contains randomization, constraints
 *   - Copy, compare, display methods
 * 
 * Layer 2: Driver
 *   - Converts transactions to pin-level activity
 *   - Receives transactions from generator
 *   - Drives DUT inputs
 * 
 * Layer 3: Monitor
 *   - Observes DUT pins
 *   - Converts pin activity to transactions
 *   - Sends transactions to scoreboard
 * 
 * Layer 4: Generator
 *   - Creates stimulus transactions
 *   - Random or directed sequences
 *   - Sends to driver
 * 
 * Layer 5: Scoreboard
 *   - Checks correctness
 *   - Compares expected vs actual
 *   - Maintains reference model
 * 
 * Layer 6: Coverage
 *   - Collects functional coverage
 *   - Tracks what has been tested
 *   - Guides stimulus generation
 * 
 * Layer 7: Environment
 *   - Connects all components
 *   - Creates mailboxes for communication
 *   - Orchestrates execution
 * 
 * Layer 8: Test
 *   - Top-level test scenario
 *   - Configures environment
 *   - Runs specific test sequence
 * 
 * COMMUNICATION:
 * - Mailboxes between layers
 * - Generator -> Driver (transactions to apply)
 * - Monitor -> Scoreboard (observed transactions)
 * 
 * BENEFITS:
 * - Separation of concerns
 * - Reusability
 * - Modularity
 * - Easier debug
 * - Scalability
 * 
 * UVM MAPPING:
 * - Transaction -> uvm_sequence_item
 * - Generator -> uvm_sequence + uvm_sequencer
 * - Driver -> uvm_driver
 * - Monitor -> uvm_monitor
 * - Scoreboard -> uvm_scoreboard
 * - Environment -> uvm_env
 * - Test -> uvm_test
 * 
 * KEY CONCEPTS:
 * 1. Abstraction: Each layer abstracts away details
 * 2. Encapsulation: Components are self-contained
 * 3. Communication: Mailboxes/TLM for inter-component
 * 4. Hierarchy: Clear structure and responsibilities
 * 5. Reuse: Components can be reused across tests
 * 
 * COMPARISON TO NON-LAYERED:
 * Non-layered:
 * - All logic in one place
 * - Hard to maintain
 * - Hard to reuse
 * - Difficult to debug
 * 
 * Layered:
 * - Clear separation
 * - Easy to maintain
 * - Highly reusable
 * - Easier to debug
 * 
 * This is the foundation that UVM builds upon!
 */
