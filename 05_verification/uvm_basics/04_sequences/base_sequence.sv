// ============================================================================
// base_sequence.sv - UVM Sequence Basics
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class simple_item extends uvm_sequence_item;
    rand bit [31:0] data;
    rand bit [7:0] addr;
    
    `uvm_object_utils_begin(simple_item)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
    `uvm_object_utils_end
    
    function new(string name = "simple_item");
        super.new(name);
    endfunction
endclass

// Base sequence class
class base_sequence extends uvm_sequence#(simple_item);
    `uvm_object_utils(base_sequence)
    
    function new(string name = "base_sequence");
        super.new(name);
    endfunction
    
    // Pre-body: executed before body()
    task pre_body();
        `uvm_info(get_type_name(), "pre_body: Starting sequence", UVM_MEDIUM)
    endtask
    
    // Main body - to be overridden
    task body();
        `uvm_info(get_type_name(), "body: Base implementation", UVM_MEDIUM)
    endtask
    
    // Post-body: executed after body()
    task post_body();
        `uvm_info(get_type_name(), "post_body: Sequence complete", UVM_MEDIUM)
    endtask
endclass

// Simple sequence - sends N items
class simple_sequence extends base_sequence;
    `uvm_object_utils(simple_sequence)
    
    int num_items = 5;
    
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    
    task body();
        simple_item item;
        
        `uvm_info(get_type_name(), $sformatf("Sending %0d items", num_items), UVM_MEDIUM)
        
        repeat(num_items) begin
            item = simple_item::type_id::create("item");
            
            start_item(item);
            assert(item.randomize());
            finish_item(item);
            
            `uvm_info(get_type_name(), $sformatf("Sent: addr=0x%0h data=0x%0h", 
                      item.addr, item.data), UVM_HIGH)
        end
    endtask
endclass

// Sequence with specific addresses
class directed_sequence extends base_sequence;
    `uvm_object_utils(directed_sequence)
    
    bit [7:0] target_addresses[];
    
    function new(string name = "directed_sequence");
        super.new(name);
        target_addresses = '{8'h10, 8'h20, 8'h30, 8'h40};
    endfunction
    
    task body();
        simple_item item;
        
        foreach(target_addresses[i]) begin
            item = simple_item::type_id::create($sformatf("item_%0d", i));
            
            start_item(item);
            assert(item.randomize() with {addr == target_addresses[i];});
            finish_item(item);
            
            `uvm_info(get_type_name(), $sformatf("Directed: addr=0x%0h data=0x%0h",
                      item.addr, item.data), UVM_MEDIUM)
        end
    endtask
endclass

// Sequence with response handling
class response_sequence extends base_sequence;
    `uvm_object_utils(response_sequence)
    
    function new(string name = "response_sequence");
        super.new(name);
    endfunction
    
    task body();
        simple_item req, rsp;
        
        repeat(3) begin
            req = simple_item::type_id::create("req");
            
            start_item(req);
            assert(req.randomize());
            finish_item(req);
            
            // Get response
            get_response(rsp);
            `uvm_info(get_type_name(), $sformatf("Got response: %s", rsp.convert2string()), UVM_MEDIUM)
        end
    endtask
endclass

typedef uvm_sequencer#(simple_item) simple_sequencer;

class simple_driver extends uvm_driver#(simple_item);
    `uvm_component_utils(simple_driver)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_item item;
        
        forever begin
            seq_item_port.get_next_item(item);
            `uvm_info(get_type_name(), $sformatf("Driving: %s", item.convert2string()), UVM_HIGH)
            #10ns;
            seq_item_port.item_done();
        end
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    simple_sequencer sequencer;
    simple_driver driver;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = simple_sequencer::type_id::create("sequencer", this);
        driver = simple_driver::type_id::create("driver", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence seq1;
        directed_sequence seq2;
        
        phase.raise_objection(this);
        
        seq1 = simple_sequence::type_id::create("seq1");
        seq1.num_items = 3;
        seq1.start(sequencer);
        
        seq2 = directed_sequence::type_id::create("seq2");
        seq2.start(sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
