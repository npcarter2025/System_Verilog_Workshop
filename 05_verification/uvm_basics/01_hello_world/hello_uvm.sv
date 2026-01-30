// ============================================================================
// hello_uvm.sv - Your First UVM Program
// ============================================================================
// This is the simplest possible UVM testbench - a "Hello World" example
// that demonstrates the basic structure of a UVM program.
//
// Key Concepts:
// 1. Import uvm_pkg
// 2. Create a test class that extends uvm_test
// 3. Use run_test() to start simulation
// 4. UVM phases (build_phase, run_phase)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// TEST CLASS
// ============================================================================
class hello_world_test extends uvm_test;
    
    // Register this class with the UVM factory
    `uvm_component_utils(hello_world_test)
    
    // Constructor
    function new(string name = "hello_world_test", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info(get_type_name(), "Constructor: Hello from new()", UVM_LOW)
    endfunction
    
    // Build phase - called automatically by UVM
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Build Phase: Constructing testbench components", UVM_LOW)
    endfunction
    
    // Run phase - where the action happens
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Run Phase: Starting simulation", UVM_LOW)
        
        // Raise objection to keep simulation alive
        phase.raise_objection(this, "Starting hello_world_test");
        
        // Main test activity
        `uvm_info(get_type_name(), "**********************************", UVM_NONE)
        `uvm_info(get_type_name(), "*                                *", UVM_NONE)
        `uvm_info(get_type_name(), "*     HELLO WORLD FROM UVM!      *", UVM_NONE)
        `uvm_info(get_type_name(), "*                                *", UVM_NONE)
        `uvm_info(get_type_name(), "**********************************", UVM_NONE)
        
        // Wait for some time
        #100ns;
        
        // Drop objection to end simulation
        phase.drop_objection(this, "Finishing hello_world_test");
        
        `uvm_info(get_type_name(), "Run Phase: Simulation complete", UVM_LOW)
    endtask
    
    // Report phase - print final statistics
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), "Report Phase: Test completed successfully!", UVM_LOW)
    endfunction
    
endclass

// ============================================================================
// TOP MODULE
// ============================================================================
module top;
    
    // Generate a clock
    logic clk = 0;
    always #5ns clk = ~clk;
    
    // Initial block to start UVM test
    initial begin
        // Print simulation start message
        $display("========================================");
        $display("Starting UVM Hello World Example");
        $display("========================================");
        
        // Run the test
        // The string "hello_world_test" must match the class name
        run_test("hello_world_test");
    end
    
    // Watchdog timer (safety mechanism)
    initial begin
        #1ms;
        $display("ERROR: Watchdog timeout!");
        $finish;
    end
    
endmodule
