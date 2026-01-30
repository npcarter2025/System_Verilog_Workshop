// ============================================================================
// base_test.sv - UVM Test Classes
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
    `uvm_object_utils_end
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

class base_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(base_sequence)
    
    function new(string name = "base_sequence");
        super.new(name);
    endfunction
    
    task body();
        transaction tr;
        repeat(5) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            finish_item(tr);
        end
    endtask
endclass

class simple_env extends uvm_env;
    `uvm_component_utils(simple_env)
    
    uvm_sequencer#(transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = uvm_sequencer#(transaction)::type_id::create("sequencer", this);
    endfunction
endclass

// Base test class - common functionality
class base_test extends uvm_test;
    `uvm_component_utils(base_test)
    
    simple_env env;
    int timeout = 1000;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create environment
        env = simple_env::type_id::create("env", this);
        
        // Configure verbosity
        if ($test$plusargs("UVM_HIGH"))
            set_report_verbosity_level_hier(UVM_HIGH);
        else if ($test$plusargs("UVM_MEDIUM"))
            set_report_verbosity_level_hier(UVM_MEDIUM);
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Test topology:", UVM_LOW)
        this.print();
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Starting %s", get_type_name()), UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        // Default: wait for timeout
        `uvm_info(get_type_name(), "Base test run_phase", UVM_MEDIUM)
        #(timeout * 1ns);
        
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        uvm_report_server svr;
        svr = uvm_report_server::get_server();
        
        `uvm_info(get_type_name(), "Test Summary:", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Errors: %0d", svr.get_severity_count(UVM_ERROR)), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Warnings: %0d", svr.get_severity_count(UVM_WARNING)), UVM_LOW)
        
        if (svr.get_severity_count(UVM_ERROR) == 0)
            `uvm_info(get_type_name(), "*** TEST PASSED ***", UVM_LOW)
        else
            `uvm_error(get_type_name(), "*** TEST FAILED ***")
    endfunction
endclass

// Specific test - runs a sequence
class simple_test extends base_test;
    `uvm_component_utils(simple_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        base_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Running simple_test", UVM_LOW)
        
        seq = base_sequence::type_id::create("seq");
        seq.start(env.sequencer);
        
        #100ns;
        
        phase.drop_objection(this);
    endtask
endclass

// Test with different configuration
class configured_test extends base_test;
    `uvm_component_utils(configured_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        // Set config before building env
        uvm_config_db#(int)::set(this, "*", "timeout", 2000);
        
        super.build_phase(phase);
    endfunction
    
    task run_phase(uvm_phase phase);
        base_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Running configured_test", UVM_LOW)
        
        // Run multiple sequences
        repeat(3) begin
            seq = base_sequence::type_id::create("seq");
            seq.start(env.sequencer);
        end
        
        #100ns;
        
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        // Can select test at runtime
        // run_test("simple_test");
        // run_test("configured_test");
        run_test();  // Uses +UVM_TESTNAME from command line
    end
endmodule
