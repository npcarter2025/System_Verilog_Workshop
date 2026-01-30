// ============================================================================
// tlm_ports.sv - UVM TLM Communication Ports
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

// Producer uses put port
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
        
        repeat(5) begin
            tr = transaction::type_id::create("tr");
            assert(tr.randomize());
            
            `uvm_info(get_type_name(), $sformatf("Putting: data=0x%0h", tr.data), UVM_MEDIUM)
            put_port.put(tr);
            #10ns;
        end
        
        phase.drop_objection(this);
    endtask
endclass

// Consumer uses get port
class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_get_port#(transaction) get_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        get_port = new("get_port", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        forever begin
            get_port.get(tr);
            `uvm_info(get_type_name(), $sformatf("Got: data=0x%0h", tr.data), UVM_MEDIUM)
        end
    endtask
endclass

// Transport connects them
class transport extends uvm_component;
    `uvm_component_utils(transport)
    
    uvm_blocking_put_export#(transaction) put_export;
    uvm_blocking_get_export#(transaction) get_export;
    
    transaction queue[$];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        put_export = new("put_export", this);
        get_export = new("get_export", this);
    endfunction
    
    task put(transaction tr);
        `uvm_info(get_type_name(), "Received transaction", UVM_HIGH)
        queue.push_back(tr);
    endtask
    
    task get(output transaction tr);
        wait(queue.size() > 0);
        tr = queue.pop_front();
        `uvm_info(get_type_name(), "Sent transaction", UVM_HIGH)
    endtask
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    producer prod;
    consumer cons;
    transport trans;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        prod = producer::type_id::create("prod", this);
        cons = consumer::type_id::create("cons", this);
        trans = transport::type_id::create("trans", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        // Connect producer to transport
        prod.put_port.connect(trans.put_export);
        
        // Connect consumer to transport
        cons.get_port.connect(trans.get_export);
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
