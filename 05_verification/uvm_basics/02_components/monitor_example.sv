// ============================================================================
// monitor_example.sv - UVM Monitor Component
// ============================================================================
// A monitor is responsible for:
// 1. Observing pin-level activity on the interface
// 2. Converting pin activity to transaction objects
// 3. Broadcasting transactions via analysis port
//
// Key Concepts:
// - Extends uvm_monitor
// - Uses virtual interface to observe signals
// - Has an analysis port to broadcast transactions
// - Passive component (never drives signals)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// TRANSACTION CLASS
// ============================================================================
class bus_transaction extends uvm_sequence_item;
    
    bit [7:0] addr;
    bit [31:0] data;
    bit we;
    time timestamp;
    
    `uvm_object_utils_begin(bus_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
        `uvm_field_int(timestamp, UVM_ALL_ON | UVM_TIME)
    `uvm_object_utils_end
    
    function new(string name = "bus_transaction");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("[@%0t] addr=0x%0h, data=0x%0h, we=%0b", 
                         timestamp, addr, data, we);
    endfunction
    
endclass

// ============================================================================
// INTERFACE
// ============================================================================
interface bus_if(input bit clk);
    logic rst_n;
    logic [7:0] addr;
    logic [31:0] data;
    logic we;
    logic valid;
    logic ready;
    
    // Monitor clocking block (all inputs)
    clocking monitor_cb @(posedge clk);
        input addr;
        input data;
        input we;
        input valid;
        input ready;
    endclocking
    
    modport monitor(clocking monitor_cb, input rst_n);
    
endinterface

// ============================================================================
// MONITOR CLASS
// ============================================================================
class bus_monitor extends uvm_monitor;
    
    `uvm_component_utils(bus_monitor)
    
    // Virtual interface
    virtual bus_if.monitor vif;
    
    // Analysis port to broadcast collected transactions
    uvm_analysis_port#(bus_transaction) ap;
    
    // Statistics
    int unsigned num_transactions;
    
    // Constructor
    function new(string name = "bus_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config_db
        if (!uvm_config_db#(virtual bus_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal(get_type_name(), "Virtual interface not found!")
        end
        
        // Create analysis port
        ap = new("ap", this);
    endfunction
    
    // Run phase - monitor loop
    task run_phase(uvm_phase phase);
        bus_transaction tr;
        
        // Wait for reset
        wait_for_reset();
        
        `uvm_info(get_type_name(), "Monitor started", UVM_MEDIUM)
        
        forever begin
            // Collect a transaction from the bus
            tr = collect_transaction();
            
            if (tr != null) begin
                // Broadcast transaction via analysis port
                ap.write(tr);
                
                num_transactions++;
                
                `uvm_info(get_type_name(), 
                          $sformatf("Collected transaction #%0d: %s", 
                                    num_transactions, tr.convert2string()),
                          UVM_HIGH)
            end
        end
    endtask
    
    // Wait for reset
    task wait_for_reset();
        `uvm_info(get_type_name(), "Waiting for reset...", UVM_HIGH)
        wait(vif.rst_n === 1'b0);
        wait(vif.rst_n === 1'b1);
        @(vif.monitor_cb);
        `uvm_info(get_type_name(), "Reset complete", UVM_HIGH)
    endtask
    
    // Collect a single transaction
    task collect_transaction();
        bus_transaction tr;
        
        // Wait for valid transaction (valid && ready handshake)
        @(vif.monitor_cb);
        while (!(vif.monitor_cb.valid && vif.monitor_cb.ready)) begin
            @(vif.monitor_cb);
        end
        
        // Create transaction
        tr = bus_transaction::type_id::create("tr");
        
        // Capture data at handshake
        tr.addr = vif.monitor_cb.addr;
        tr.data = vif.monitor_cb.data;
        tr.we = vif.monitor_cb.we;
        tr.timestamp = $time;
        
        `uvm_info(get_type_name(), 
                  "Transaction handshake detected", 
                  UVM_DEBUG)
        
        return tr;
    endtask
    
    // Report phase - print statistics
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Total transactions monitored: %0d", num_transactions),
                  UVM_LOW)
    endfunction
    
endclass

// ============================================================================
// SUBSCRIBER (receives transactions from monitor)
// ============================================================================
class transaction_subscriber extends uvm_subscriber#(bus_transaction);
    
    `uvm_component_utils(transaction_subscriber)
    
    int unsigned write_count;
    int unsigned read_count;
    
    function new(string name = "transaction_subscriber", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // This function is called automatically when monitor broadcasts
    function void write(bus_transaction t);
        `uvm_info(get_type_name(), 
                  $sformatf("Received: %s", t.convert2string()),
                  UVM_MEDIUM)
        
        // Count write vs read transactions
        if (t.we) write_count++;
        else read_count++;
    endfunction
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Statistics: %0d writes, %0d reads", 
                            write_count, read_count),
                  UVM_LOW)
    endfunction
    
endclass

// ============================================================================
// SIMPLE ENV
// ============================================================================
class monitor_env extends uvm_env;
    
    `uvm_component_utils(monitor_env)
    
    bus_monitor monitor;
    transaction_subscriber subscriber;
    
    function new(string name = "monitor_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        monitor = bus_monitor::type_id::create("monitor", this);
        subscriber = transaction_subscriber::type_id::create("subscriber", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor's analysis port to subscriber's analysis export
        monitor.ap.connect(subscriber.analysis_export);
    endfunction
    
endclass

// ============================================================================
// TEST
// ============================================================================
class monitor_test extends uvm_test;
    
    `uvm_component_utils(monitor_test)
    
    monitor_env env;
    
    function new(string name = "monitor_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = monitor_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting monitor test...", UVM_LOW)
        
        // Just wait - the monitor will observe DUT activity
        #1us;
        
        phase.drop_objection(this);
        `uvm_info(get_type_name(), "Monitor test complete!", UVM_LOW)
    endtask
    
endclass

// ============================================================================
// SIMPLE TRAFFIC GENERATOR (simulates DUT activity)
// ============================================================================
module traffic_generator(bus_if bif);
    
    // Generate some bus transactions
    initial begin
        wait(bif.rst_n);
        @(posedge bif.clk);
        
        repeat(10) begin
            // Random delay
            repeat($urandom_range(1, 3)) @(posedge bif.clk);
            
            // Drive a transaction
            bif.valid <= 1'b1;
            bif.addr <= $urandom_range(0, 255);
            bif.data <= $urandom();
            bif.we <= $urandom_range(0, 1);
            bif.ready <= 1'b1;
            
            @(posedge bif.clk);
            
            bif.valid <= 1'b0;
            bif.ready <= 1'b0;
        end
    end
    
endmodule

// ============================================================================
// TOP MODULE
// ============================================================================
module top;
    
    bit clk = 0;
    always #5ns clk = ~clk;
    
    bus_if bif(clk);
    
    traffic_generator tgen(bif);
    
    initial begin
        // Reset sequence
        bif.rst_n = 0;
        bif.valid = 0;
        bif.ready = 0;
        #20ns;
        bif.rst_n = 1;
        
        // Store interface in config_db
        uvm_config_db#(virtual bus_if)::set(null, "*", "vif", bif);
        
        // Run test
        run_test("monitor_test");
    end
    
    // Watchdog
    initial begin
        #10us;
        $display("Simulation complete");
        $finish;
    end
    
endmodule
