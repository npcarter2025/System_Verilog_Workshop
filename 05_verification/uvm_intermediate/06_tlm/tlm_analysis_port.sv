// ============================================================================
// tlm_analysis_port.sv - UVM Analysis Ports (Broadcast)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(transaction)
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Monitor broadcasts via analysis port
class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        phase.raise_objection(this);
        
        repeat(10) begin
            tr = transaction::type_id::create("tr");
            assert(tr.randomize());
            
            `uvm_info(get_type_name(), $sformatf("Broadcasting: data=0x%0h", tr.data), UVM_MEDIUM)
            ap.write(tr);
            #10ns;
        end
        
        phase.drop_objection(this);
    endtask
endclass

// Subscriber 1
class subscriber1 extends uvm_subscriber#(transaction);
    `uvm_component_utils(subscriber1)
    
    int count = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void write(transaction t);
        count++;
        `uvm_info(get_type_name(), $sformatf("Received #%0d: data=0x%0h", count, t.data), UVM_MEDIUM)
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Total received: %0d", count), UVM_LOW)
    endfunction
endclass

// Subscriber 2 (different implementation)
class subscriber2 extends uvm_component;
    `uvm_component_utils(subscriber2)
    
    uvm_analysis_export#(transaction) analysis_export;
    int sum = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        analysis_export = new("analysis_export", this);
    endfunction
    
    function void write(transaction t);
        sum += t.data;
        `uvm_info(get_type_name(), $sformatf("Running sum: %0d", sum), UVM_HIGH)
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Sum of all data: %0d", sum), UVM_LOW)
    endfunction
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    monitor mon;
    subscriber1 sub1;
    subscriber2 sub2;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        mon = monitor::type_id::create("mon", this);
        sub1 = subscriber1::type_id::create("sub1", this);
        sub2 = subscriber2::type_id::create("sub2", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        // Connect monitor to both subscribers (broadcast)
        mon.ap.connect(sub1.analysis_export);
        mon.ap.connect(sub2.analysis_export);
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #200ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
