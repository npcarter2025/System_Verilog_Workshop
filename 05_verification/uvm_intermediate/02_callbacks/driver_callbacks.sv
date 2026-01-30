// ============================================================================
// driver_callbacks.sv - UVM Callbacks
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [31:0] data;
    `uvm_object_utils(transaction)
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Callback class - defines callback methods
class driver_callback extends uvm_callback;
    `uvm_object_utils(driver_callback)
    
    function new(string name = "driver_callback");
        super.new(name);
    endfunction
    
    // Virtual methods to be overridden
    virtual task pre_send(transaction tr);
    endtask
    
    virtual task post_send(transaction tr);
    endtask
endclass

// Driver with callback support
class my_driver extends uvm_driver#(transaction);
    `uvm_component_utils(my_driver)
    `uvm_register_cb(my_driver, driver_callback)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        forever begin
            seq_item_port.get_next_item(tr);
            
            // Execute pre_send callbacks
            `uvm_do_callbacks(my_driver, driver_callback, pre_send(tr))
            
            // Drive transaction
            `uvm_info(get_type_name(), $sformatf("Driving: data=0x%0h", tr.data), UVM_MEDIUM)
            #10ns;
            
            // Execute post_send callbacks
            `uvm_do_callbacks(my_driver, driver_callback, post_send(tr))
            
            seq_item_port.item_done();
        end
    endtask
endclass

// Specific callback implementations
class inject_error_callback extends driver_callback;
    `uvm_object_utils(inject_error_callback)
    
    function new(string name = "inject_error_callback");
        super.new(name);
    endfunction
    
    task pre_send(transaction tr);
        if ($urandom_range(0, 9) == 0) begin  // 10% chance
            tr.data = 32'hBAD_DATA;
            `uvm_info("CALLBACK", "Injecting error!", UVM_MEDIUM)
        end
    endtask
endclass

class delay_callback extends driver_callback;
    `uvm_object_utils(delay_callback)
    
    int delay_cycles;
    
    function new(string name = "delay_callback");
        super.new(name);
        delay_cycles = 5;
    endfunction
    
    task pre_send(transaction tr);
        `uvm_info("CALLBACK", $sformatf("Adding %0d cycle delay", delay_cycles), UVM_HIGH)
        repeat(delay_cycles) #10ns;
    endtask
endclass

class logging_callback extends driver_callback;
    `uvm_object_utils(logging_callback)
    
    int transaction_count = 0;
    
    function new(string name = "logging_callback");
        super.new(name);
    endfunction
    
    task post_send(transaction tr);
        transaction_count++;
        `uvm_info("CALLBACK", $sformatf("Transaction #%0d: data=0x%0h", 
                  transaction_count, tr.data), UVM_MEDIUM)
    endtask
endclass

class simple_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(simple_sequence)
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    task body();
        repeat(10) begin
            req = transaction::type_id::create("req");
            start_item(req);
            assert(req.randomize());
            finish_item(req);
        end
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    my_driver driver;
    uvm_sequencer#(transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        driver = my_driver::type_id::create("driver", this);
        sequencer = uvm_sequencer#(transaction)::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        inject_error_callback err_cb;
        delay_callback dly_cb;
        logging_callback log_cb;
        
        // Create and register callbacks
        err_cb = inject_error_callback::type_id::create("err_cb");
        dly_cb = delay_callback::type_id::create("dly_cb");
        log_cb = logging_callback::type_id::create("log_cb");
        
        // Add callbacks to driver
        uvm_callbacks#(my_driver, driver_callback)::add(driver, err_cb);
        uvm_callbacks#(my_driver, driver_callback)::add(driver, dly_cb);
        uvm_callbacks#(my_driver, driver_callback)::add(driver, log_cb);
        
        `uvm_info("TEST", "Callbacks registered", UVM_LOW)
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
    initial run_test("test");
endmodule
