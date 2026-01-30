// ============================================================================
// factory_override.sv - UVM Factory Overrides
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class base_transaction extends uvm_sequence_item;
    rand bit [7:0] data;
    
    `uvm_object_utils_begin(base_transaction)
        `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "base_transaction");
        super.new(name);
    endfunction
    
    virtual function string get_type_name_custom();
        return "BASE";
    endfunction
endclass

class extended_transaction extends base_transaction;
    rand bit [7:0] extra_field;
    
    `uvm_object_utils_begin(extended_transaction)
        `uvm_field_int(extra_field, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "extended_transaction");
        super.new(name);
    endfunction
    
    function string get_type_name_custom();
        return "EXTENDED";
    endfunction
endclass

class base_driver extends uvm_driver#(base_transaction);
    `uvm_component_utils(base_driver)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        base_transaction tr;
        forever begin
            seq_item_port.get_next_item(tr);
            `uvm_info(get_type_name(), $sformatf("Base driver got: %s", 
                      tr.get_type_name_custom()), UVM_MEDIUM)
            #10ns;
            seq_item_port.item_done();
        end
    endtask
endclass

class enhanced_driver extends base_driver;
    `uvm_component_utils(enhanced_driver)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        base_transaction tr;
        forever begin
            seq_item_port.get_next_item(tr);
            `uvm_info(get_type_name(), $sformatf("Enhanced driver got: %s (with extra features!)", 
                      tr.get_type_name_custom()), UVM_MEDIUM)
            #10ns;
            seq_item_port.item_done();
        end
    endtask
endclass

class simple_sequence extends uvm_sequence#(base_transaction);
    `uvm_object_utils(simple_sequence)
    
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    
    task body();
        repeat(5) begin
            req = base_transaction::type_id::create("req");
            start_item(req);
            assert(req.randomize());
            finish_item(req);
            `uvm_info(get_type_name(), $sformatf("Created: %s", req.get_type_name_custom()), UVM_HIGH)
        end
    endtask
endclass

class test_no_override extends uvm_test;
    `uvm_component_utils(test_no_override)
    
    base_driver driver;
    uvm_sequencer#(base_transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "No overrides - using base classes", UVM_LOW)
        
        driver = base_driver::type_id::create("driver", this);
        sequencer = uvm_sequencer#(base_transaction)::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence seq;
        
        phase.raise_objection(this);
        seq = simple_sequence::type_id::create("seq");
        seq.start(sequencer);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

class test_with_override extends uvm_test;
    `uvm_component_utils(test_with_override)
    
    base_driver driver;
    uvm_sequencer#(base_transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Using factory overrides", UVM_LOW)
        
        // Type override: replace all base_transactions with extended_transactions
        base_transaction::type_id::set_type_override(extended_transaction::get_type());
        
        // Type override: replace all base_drivers with enhanced_drivers
        base_driver::type_id::set_type_override(enhanced_driver::get_type());
        
        driver = base_driver::type_id::create("driver", this);
        sequencer = uvm_sequencer#(base_transaction)::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence seq;
        
        phase.raise_objection(this);
        seq = simple_sequence::type_id::create("seq");
        seq.start(sequencer);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        // Run with: +UVM_TESTNAME=test_no_override
        // Or:       +UVM_TESTNAME=test_with_override
        run_test();
    end
endmodule
