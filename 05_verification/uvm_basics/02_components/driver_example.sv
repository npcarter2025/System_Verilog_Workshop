// ============================================================================
// driver_example.sv - UVM Driver Component
// ============================================================================
// A driver is responsible for:
// 1. Getting transactions from a sequencer
// 2. Converting transactions to pin-level activity
// 3. Driving signals to the DUT
//
// Key Concepts:
// - Extends uvm_driver
// - Uses seq_item_port to get transactions
// - Parameterized with transaction type
// - Uses virtual interface to drive signals
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// SIMPLE TRANSACTION CLASS
// ============================================================================
class simple_transaction extends uvm_sequence_item;
    
    rand bit [7:0] addr;
    rand bit [31:0] data;
    rand bit we;  // write enable
    
    `uvm_object_utils_begin(simple_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "simple_transaction");
        super.new(name);
    endfunction
    
    // Custom display
    function string convert2string();
        return $sformatf("addr=0x%0h, data=0x%0h, we=%0b", addr, data, we);
    endfunction
    
endclass

// ============================================================================
// SIMPLE INTERFACE
// ============================================================================
interface simple_if(input bit clk);
    logic rst_n;
    logic [7:0] addr;
    logic [31:0] wdata;
    logic we;
    logic ready;
    
    // Clocking block for driver (outputs)
    clocking driver_cb @(posedge clk);
        output addr;
        output wdata;
        output we;
        input ready;
    endclocking
    
    modport driver(clocking driver_cb, input rst_n);
    modport dut(input addr, input wdata, input we, output ready, input rst_n);
    
endinterface

// ============================================================================
// DRIVER CLASS
// ============================================================================
class simple_driver extends uvm_driver#(simple_transaction);
    
    `uvm_component_utils(simple_driver)
    
    // Virtual interface to DUT
    virtual simple_if.driver vif;
    
    // Constructor
    function new(string name = "simple_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - get virtual interface from config_db
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual simple_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal(get_type_name(), "Virtual interface not found!")
        end
    endfunction
    
    // Run phase - main driver loop
    task run_phase(uvm_phase phase);
        simple_transaction tr;
        
        // Wait for reset to complete
        wait_for_reset();
        
        forever begin
            // Get next transaction from sequencer
            // This blocks until a transaction is available
            seq_item_port.get_next_item(tr);
            
            `uvm_info(get_type_name(), 
                      $sformatf("Driving transaction: %s", tr.convert2string()), 
                      UVM_MEDIUM)
            
            // Drive the transaction to the DUT
            drive_transaction(tr);
            
            // Tell sequencer we're done with this transaction
            seq_item_port.item_done();
        end
    endtask
    
    // Wait for reset to complete
    task wait_for_reset();
        `uvm_info(get_type_name(), "Waiting for reset...", UVM_HIGH)
        wait(vif.rst_n === 1'b0);
        wait(vif.rst_n === 1'b1);
        @(vif.driver_cb);  // Wait one clock after reset
        `uvm_info(get_type_name(), "Reset complete", UVM_HIGH)
    endtask
    
    // Drive a single transaction
    task drive_transaction(simple_transaction tr);
        // Wait for DUT to be ready
        while (!vif.driver_cb.ready) begin
            @(vif.driver_cb);
        end
        
        // Drive signals
        vif.driver_cb.addr <= tr.addr;
        vif.driver_cb.wdata <= tr.data;
        vif.driver_cb.we <= tr.we;
        
        // Wait one clock
        @(vif.driver_cb);
        
        // De-assert signals
        vif.driver_cb.we <= 1'b0;
        
        `uvm_info(get_type_name(), "Transaction driven", UVM_HIGH)
    endtask
    
endclass

// ============================================================================
// DUMMY DUT (for demonstration)
// ============================================================================
module dummy_dut(simple_if.dut dif);
    
    // Always ready for simplicity
    assign dif.ready = 1'b1;
    
    // Print received transactions
    always @(posedge dif.we) begin
        if (dif.rst_n) begin
            $display("[DUT] Received: addr=0x%0h, data=0x%0h", 
                     dif.addr, dif.wdata);
        end
    end
    
endmodule

// ============================================================================
// SIMPLE SEQUENCE
// ============================================================================
class simple_sequence extends uvm_sequence#(simple_transaction);
    
    `uvm_object_utils(simple_sequence)
    
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    
    task body();
        simple_transaction tr;
        
        repeat(5) begin
            tr = simple_transaction::type_id::create("tr");
            
            start_item(tr);
            
            // Randomize transaction
            if (!tr.randomize()) begin
                `uvm_error(get_type_name(), "Randomization failed")
            end
            
            finish_item(tr);
        end
    endtask
    
endclass

// ============================================================================
// SEQUENCER
// ============================================================================
typedef uvm_sequencer#(simple_transaction) simple_sequencer;

// ============================================================================
// SIMPLE AGENT
// ============================================================================
class simple_agent extends uvm_agent;
    
    `uvm_component_utils(simple_agent)
    
    simple_driver driver;
    simple_sequencer sequencer;
    
    function new(string name = "simple_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        driver = simple_driver::type_id::create("driver", this);
        sequencer = simple_sequencer::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver's seq_item_port to sequencer's seq_item_export
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
endclass

// ============================================================================
// TEST
// ============================================================================
class driver_test extends uvm_test;
    
    `uvm_component_utils(driver_test)
    
    simple_agent agent;
    
    function new(string name = "driver_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = simple_agent::type_id::create("agent", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting driver test...", UVM_LOW)
        
        seq = simple_sequence::type_id::create("seq");
        seq.start(agent.sequencer);
        
        #100ns;
        
        phase.drop_objection(this);
        `uvm_info(get_type_name(), "Driver test complete!", UVM_LOW)
    endtask
    
endclass

// ============================================================================
// TOP MODULE
// ============================================================================
module top;
    
    bit clk = 0;
    always #5ns clk = ~clk;
    
    simple_if sif(clk);
    
    dummy_dut dut(sif);
    
    initial begin
        // Reset sequence
        sif.rst_n = 0;
        #20ns;
        sif.rst_n = 1;
        
        // Store interface in config_db
        uvm_config_db#(virtual simple_if)::set(null, "*", "vif", sif);
        
        // Run test
        run_test("driver_test");
    end
    
    // Watchdog
    initial begin
        #10us;
        $display("ERROR: Timeout!");
        $finish;
    end
    
endmodule
