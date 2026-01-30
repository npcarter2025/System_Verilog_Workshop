// ============================================================================
// test_variations.sv - Different Test Patterns
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class packet extends uvm_sequence_item;
    rand bit [7:0] data;
    constraint data_c {data inside {[1:255]};}
    `uvm_object_utils(packet)
    function new(string name = "packet");
        super.new(name);
    endfunction
endclass

class short_seq extends uvm_sequence#(packet);
    `uvm_object_utils(short_seq)
    function new(string name = "short_seq");
        super.new(name);
    endfunction
    task body();
        repeat(5) begin
            req = packet::type_id::create("req");
            start_item(req);
            assert(req.randomize());
            finish_item(req);
        end
    endtask
endclass

class long_seq extends uvm_sequence#(packet);
    `uvm_object_utils(long_seq)
    function new(string name = "long_seq");
        super.new(name);
    endfunction
    task body();
        repeat(100) begin
            req = packet::type_id::create("req");
            start_item(req);
            assert(req.randomize());
            finish_item(req);
        end
    endtask
endclass

class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    uvm_sequencer#(packet) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = uvm_sequencer#(packet)::type_id::create("sequencer", this);
    endfunction
endclass

// Smoke test - quick sanity check
class smoke_test extends uvm_test;
    `uvm_component_utils(smoke_test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        short_seq seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Running smoke test - quick validation", UVM_LOW)
        
        seq = short_seq::type_id::create("seq");
        seq.start(env.sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

// Stress test - long duration
class stress_test extends uvm_test;
    `uvm_component_utils(stress_test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        long_seq seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Running stress test - extended duration", UVM_LOW)
        
        repeat(10) begin
            seq = long_seq::type_id::create("seq");
            seq.start(env.sequencer);
        end
        
        #1us;
        phase.drop_objection(this);
    endtask
endclass

// Regression test - multiple scenarios
class regression_test extends uvm_test;
    `uvm_component_utils(regression_test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        short_seq short_s;
        long_seq long_s;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Running regression test - comprehensive coverage", UVM_LOW)
        
        // Multiple test scenarios
        repeat(3) begin
            short_s = short_seq::type_id::create("short_s");
            short_s.start(env.sequencer);
            
            long_s = long_seq::type_id::create("long_s");
            long_s.start(env.sequencer);
        end
        
        #500ns;
        phase.drop_objection(this);
    endtask
endclass

// Debug test - high verbosity
class debug_test extends uvm_test;
    `uvm_component_utils(debug_test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
        set_report_verbosity_level_hier(UVM_DEBUG);
    endfunction
    
    task run_phase(uvm_phase phase);
        short_seq seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Running debug test - maximum verbosity", UVM_LOW)
        
        seq = short_seq::type_id::create("seq");
        seq.start(env.sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        // Select test:
        // +UVM_TESTNAME=smoke_test
        // +UVM_TESTNAME=stress_test
        // +UVM_TESTNAME=regression_test
        // +UVM_TESTNAME=debug_test
        run_test();
    end
endmodule
