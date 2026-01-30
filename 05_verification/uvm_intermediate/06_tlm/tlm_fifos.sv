// ============================================================================
// tlm_fifos.sv - UVM TLM FIFOs
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

class producer extends uvm_component;
    `uvm_component_utils(producer)
    
    uvm_blocking_put_port#(transaction) put_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        put_port = new("put_port", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        phase.raise_objection(this);
        
        repeat(20) begin
            tr = transaction::type_id::create("tr");
            assert(tr.randomize());
            
            `uvm_info(get_type_name(), $sformatf("Producing: data=0x%0h", tr.data), UVM_HIGH)
            put_port.put(tr);
            #5ns;  // Fast producer
        end
        
        phase.drop_objection(this);
    endtask
endclass

class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_get_port#(transaction) get_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        get_port = new("get_port", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        repeat(20) begin
            get_port.get(tr);
            `uvm_info(get_type_name(), $sformatf("Consuming: data=0x%0h", tr.data), UVM_MEDIUM)
            #15ns;  // Slow consumer
        end
    endtask
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    producer prod;
    consumer cons;
    uvm_tlm_fifo#(transaction) fifo;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        prod = producer::type_id::create("prod", this);
        cons = consumer::type_id::create("cons", this);
        
        // Create FIFO with depth 8
        fifo = new("fifo", this, 8);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        // Connect producer and consumer to FIFO
        prod.put_port.connect(fifo.blocking_put_export);
        cons.get_port.connect(fifo.blocking_get_export);
    endfunction
    
    task run_phase(uvm_phase phase);
        fork
            // Monitor FIFO status
            forever begin
                #10ns;
                `uvm_info(get_type_name(), $sformatf("FIFO status: used=%0d/%0d", 
                          fifo.used(), fifo.size()), UVM_HIGH)
            end
        join_none
    endtask
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
        #500ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
