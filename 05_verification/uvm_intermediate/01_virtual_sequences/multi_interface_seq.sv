// ============================================================================
// multi_interface_seq.sv - Complex Multi-Interface Virtual Sequences
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class cmd_tr extends uvm_sequence_item;
    rand bit [7:0] cmd;
    `uvm_object_utils(cmd_tr)
    function new(string name = "cmd_tr");
        super.new(name);
    endfunction
endclass

class data_tr extends uvm_sequence_item;
    rand bit [31:0] data;
    `uvm_object_utils(data_tr)
    function new(string name = "data_tr");
        super.new(name);
    endfunction
endclass

class status_tr extends uvm_sequence_item;
    bit [7:0] status;
    `uvm_object_utils(status_tr)
    function new(string name = "status_tr");
        super.new(name);
    endfunction
endclass

typedef uvm_sequencer#(cmd_tr) cmd_sequencer;
typedef uvm_sequencer#(data_tr) data_sequencer;
typedef uvm_sequencer#(status_tr) status_sequencer;

class virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(virtual_sequencer)
    
    cmd_sequencer cmd_seqr;
    data_sequencer data_seqr;
    status_sequencer status_seqr;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

// Write transaction: cmd + data
class write_transaction_seq extends uvm_sequence;
    `uvm_object_utils(write_transaction_seq)
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    rand bit [31:0] addr;
    rand bit [31:0] data;
    
    function new(string name = "write_transaction_seq");
        super.new(name);
    endfunction
    
    task body();
        cmd_tr cmd;
        data_tr dat;
        
        // Send command
        cmd = cmd_tr::type_id::create("cmd");
        cmd.cmd = 8'h01;  // WRITE command
        cmd.start(p_sequencer.cmd_seqr);
        
        // Send data
        dat = data_tr::type_id::create("dat");
        dat.data = data;
        dat.start(p_sequencer.data_seqr);
        
        `uvm_info(get_type_name(), $sformatf("Write: addr=0x%0h data=0x%0h", addr, data), UVM_MEDIUM)
    endtask
endclass

// Read transaction: cmd + wait for status
class read_transaction_seq extends uvm_sequence;
    `uvm_object_utils(read_transaction_seq)
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    rand bit [31:0] addr;
    bit [31:0] read_data;
    
    function new(string name = "read_transaction_seq");
        super.new(name);
    endfunction
    
    task body();
        cmd_tr cmd;
        
        // Send command
        cmd = cmd_tr::type_id::create("cmd");
        cmd.cmd = 8'h02;  // READ command
        cmd.start(p_sequencer.cmd_seqr);
        
        // Wait for response (in real scenario, monitor would capture this)
        #50ns;
        
        `uvm_info(get_type_name(), $sformatf("Read: addr=0x%0h", addr), UVM_MEDIUM)
    endtask
endclass

// Burst write sequence
class burst_write_seq extends uvm_sequence;
    `uvm_object_utils(burst_write_seq)
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    rand int num_beats;
    constraint num_beats_c {num_beats inside {[4:16]};}
    
    function new(string name = "burst_write_seq");
        super.new(name);
    endfunction
    
    task body();
        write_transaction_seq wr_seq;
        
        assert(this.randomize());
        
        `uvm_info(get_type_name(), $sformatf("Burst write: %0d beats", num_beats), UVM_MEDIUM)
        
        repeat(num_beats) begin
            wr_seq = write_transaction_seq::type_id::create("wr_seq");
            assert(wr_seq.randomize());
            wr_seq.start(p_sequencer);
        end
    endtask
endclass

class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    
    cmd_sequencer cmd_seqr;
    data_sequencer data_seqr;
    status_sequencer status_seqr;
    virtual_sequencer v_seqr;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        cmd_seqr = cmd_sequencer::type_id::create("cmd_seqr", this);
        data_seqr = data_sequencer::type_id::create("data_seqr", this);
        status_seqr = status_sequencer::type_id::create("status_seqr", this);
        v_seqr = virtual_sequencer::type_id::create("v_seqr", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        v_seqr.cmd_seqr = cmd_seqr;
        v_seqr.data_seqr = data_seqr;
        v_seqr.status_seqr = status_seqr;
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        write_transaction_seq wr_seq;
        read_transaction_seq rd_seq;
        burst_write_seq burst_seq;
        
        phase.raise_objection(this);
        
        // Single write
        wr_seq = write_transaction_seq::type_id::create("wr_seq");
        wr_seq.addr = 32'h1000;
        wr_seq.data = 32'hDEADBEEF;
        wr_seq.start(env.v_seqr);
        
        // Single read
        rd_seq = read_transaction_seq::type_id::create("rd_seq");
        rd_seq.addr = 32'h1000;
        rd_seq.start(env.v_seqr);
        
        // Burst
        burst_seq = burst_write_seq::type_id::create("burst_seq");
        burst_seq.start(env.v_seqr);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
