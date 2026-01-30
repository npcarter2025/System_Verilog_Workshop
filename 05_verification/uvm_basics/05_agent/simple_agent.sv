// ============================================================================
// simple_agent.sv - Complete UVM Agent Example
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Transaction
class bus_transaction extends uvm_sequence_item;
    rand bit [15:0] addr;
    rand bit [31:0] data;
    rand bit wr_rd;
    
    `uvm_object_utils_begin(bus_transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(wr_rd, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "bus_transaction");
        super.new(name);
    endfunction
endclass

// Interface
interface bus_if(input bit clk);
    logic rst_n;
    logic [15:0] addr;
    logic [31:0] data;
    logic valid;
    logic ready;
    logic wr_rd;
    
    clocking driver_cb @(posedge clk);
        output addr, data, valid, wr_rd;
        input ready;
    endclocking
    
    clocking monitor_cb @(posedge clk);
        input addr, data, valid, ready, wr_rd;
    endclocking
    
    modport driver(clocking driver_cb, input rst_n);
    modport monitor(clocking monitor_cb, input rst_n);
endinterface

// Driver
class bus_driver extends uvm_driver#(bus_transaction);
    `uvm_component_utils(bus_driver)
    
    virtual bus_if.driver vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(virtual bus_if)::get(this, "", "vif", vif))
            `uvm_fatal(get_type_name(), "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        bus_transaction tr;
        
        vif.driver_cb.valid <= 0;
        wait(vif.rst_n);
        @(vif.driver_cb);
        
        forever begin
            seq_item_port.get_next_item(tr);
            drive_transaction(tr);
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(bus_transaction tr);
        vif.driver_cb.addr <= tr.addr;
        vif.driver_cb.data <= tr.data;
        vif.driver_cb.wr_rd <= tr.wr_rd;
        vif.driver_cb.valid <= 1'b1;
        
        @(vif.driver_cb);
        while (!vif.driver_cb.ready) @(vif.driver_cb);
        
        vif.driver_cb.valid <= 1'b0;
        `uvm_info(get_type_name(), $sformatf("Drove: addr=0x%0h data=0x%0h wr=%0b", 
                  tr.addr, tr.data, tr.wr_rd), UVM_HIGH)
    endtask
endclass

// Monitor
class bus_monitor extends uvm_monitor;
    `uvm_component_utils(bus_monitor)
    
    virtual bus_if.monitor vif;
    uvm_analysis_port#(bus_transaction) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(virtual bus_if)::get(this, "", "vif", vif))
            `uvm_fatal(get_type_name(), "Virtual interface not found")
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        bus_transaction tr;
        
        wait(vif.rst_n);
        @(vif.monitor_cb);
        
        forever begin
            @(vif.monitor_cb);
            if (vif.monitor_cb.valid && vif.monitor_cb.ready) begin
                tr = bus_transaction::type_id::create("tr");
                tr.addr = vif.monitor_cb.addr;
                tr.data = vif.monitor_cb.data;
                tr.wr_rd = vif.monitor_cb.wr_rd;
                
                ap.write(tr);
                `uvm_info(get_type_name(), $sformatf("Monitored: %s", tr.convert2string()), UVM_HIGH)
            end
        end
    endtask
endclass

// Sequencer
typedef uvm_sequencer#(bus_transaction) bus_sequencer;

// Agent
class bus_agent extends uvm_agent;
    `uvm_component_utils(bus_agent)
    
    bus_driver driver;
    bus_monitor monitor;
    bus_sequencer sequencer;
    
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        monitor = bus_monitor::type_id::create("monitor", this);
        
        if (is_active == UVM_ACTIVE) begin
            driver = bus_driver::type_id::create("driver", this);
            sequencer = bus_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass

// Simple sequence
class simple_sequence extends uvm_sequence#(bus_transaction);
    `uvm_object_utils(simple_sequence)
    
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    
    task body();
        bus_transaction tr;
        repeat(5) begin
            tr = bus_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            finish_item(tr);
        end
    endtask
endclass

// Test
class agent_test extends uvm_test;
    `uvm_component_utils(agent_test)
    
    bus_agent agent;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        agent = bus_agent::type_id::create("agent", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence seq;
        
        phase.raise_objection(this);
        
        seq = simple_sequence::type_id::create("seq");
        seq.start(agent.sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

// Testbench
module tb;
    bit clk = 0;
    always #5 clk = ~clk;
    
    bus_if bif(clk);
    
    initial begin
        bif.rst_n = 0;
        bif.ready = 1;
        #20 bif.rst_n = 1;
        
        uvm_config_db#(virtual bus_if)::set(null, "*", "vif", bif);
        run_test("agent_test");
    end
endmodule
