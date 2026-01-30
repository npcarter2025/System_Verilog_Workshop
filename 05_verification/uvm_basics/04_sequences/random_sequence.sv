// ============================================================================
// random_sequence.sv - Random and Constrained-Random Sequences
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class mem_transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit        wr_rd;
    rand int        delay;
    
    constraint addr_range_c {addr inside {[32'h1000:32'h1FFF]};}
    constraint delay_c {delay inside {[0:5]};}
    
    `uvm_object_utils_begin(mem_transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(wr_rd, UVM_ALL_ON)
        `uvm_field_int(delay, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "mem_transaction");
        super.new(name);
    endfunction
endclass

// Fully random sequence
class random_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(random_sequence)
    
    rand int num_trans;
    constraint num_trans_c {num_trans inside {[5:20]};}
    
    function new(string name = "random_sequence");
        super.new(name);
    endfunction
    
    task body();
        mem_transaction tr;
        
        assert(this.randomize());
        `uvm_info(get_type_name(), $sformatf("Generating %0d random transactions", num_trans), UVM_MEDIUM)
        
        repeat(num_trans) begin
            tr = mem_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            finish_item(tr);
        end
    endtask
endclass

// Constrained random - write-only
class write_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(write_sequence)
    
    function new(string name = "write_sequence");
        super.new(name);
    endfunction
    
    task body();
        mem_transaction tr;
        
        repeat(10) begin
            tr = mem_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                wr_rd == 1'b1;  // Write only
                data != 32'h0;   // Non-zero data
            });
            finish_item(tr);
        end
    endtask
endclass

// Constrained random - specific address range
class address_range_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(address_range_sequence)
    
    bit [31:0] start_addr;
    bit [31:0] end_addr;
    
    function new(string name = "address_range_sequence");
        super.new(name);
        start_addr = 32'h2000;
        end_addr = 32'h2FFF;
    endfunction
    
    task body();
        mem_transaction tr;
        
        repeat(15) begin
            tr = mem_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                addr inside {[start_addr:end_addr]};
                addr[1:0] == 2'b00;  // Word aligned
            });
            finish_item(tr);
        end
    endtask
endclass

// Burst sequence - sequential addresses
class burst_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(burst_sequence)
    
    rand bit [31:0] burst_addr;
    rand int burst_length;
    
    constraint burst_length_c {burst_length inside {[4:16]};}
    
    function new(string name = "burst_sequence");
        super.new(name);
    endfunction
    
    task body();
        mem_transaction tr;
        
        assert(this.randomize());
        `uvm_info(get_type_name(), $sformatf("Burst: addr=0x%0h len=%0d", burst_addr, burst_length), UVM_MEDIUM)
        
        for (int i = 0; i < burst_length; i++) begin
            tr = mem_transaction::type_id::create($sformatf("tr_%0d", i));
            start_item(tr);
            assert(tr.randomize() with {
                addr == burst_addr + (i * 4);
                wr_rd == 1'b1;
            });
            finish_item(tr);
        end
    endtask
endclass

// Weighted random - 70% writes, 30% reads
class weighted_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(weighted_sequence)
    
    function new(string name = "weighted_sequence");
        super.new(name);
    endfunction
    
    task body();
        mem_transaction tr;
        
        repeat(20) begin
            tr = mem_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                wr_rd dist {1'b1 := 70, 1'b0 := 30};
            });
            finish_item(tr);
        end
    endtask
endclass

// Alternating pattern
class alternating_sequence extends uvm_sequence#(mem_transaction);
    `uvm_object_utils(alternating_sequence)
    
    bit next_is_write = 1;
    
    function new(string name = "alternating_sequence");
        super.new(name);
    endfunction
    
    task body();
        mem_transaction tr;
        
        repeat(10) begin
            tr = mem_transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                wr_rd == next_is_write;
            });
            finish_item(tr);
            next_is_write = ~next_is_write;
        end
    endtask
endclass

typedef uvm_sequencer#(mem_transaction) mem_sequencer;

class test extends uvm_test;
    `uvm_component_utils(test)
    mem_sequencer sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = mem_sequencer::type_id::create("sequencer", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        random_sequence rand_seq;
        write_sequence wr_seq;
        burst_sequence burst_seq;
        weighted_sequence weight_seq;
        alternating_sequence alt_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== Random Sequence ===", UVM_LOW)
        rand_seq = random_sequence::type_id::create("rand_seq");
        rand_seq.start(sequencer);
        
        `uvm_info("TEST", "=== Write-Only Sequence ===", UVM_LOW)
        wr_seq = write_sequence::type_id::create("wr_seq");
        wr_seq.start(sequencer);
        
        `uvm_info("TEST", "=== Burst Sequence ===", UVM_LOW)
        burst_seq = burst_sequence::type_id::create("burst_seq");
        burst_seq.start(sequencer);
        
        `uvm_info("TEST", "=== Weighted Sequence ===", UVM_LOW)
        weight_seq = weighted_sequence::type_id::create("weight_seq");
        weight_seq.start(sequencer);
        
        `uvm_info("TEST", "=== Alternating Sequence ===", UVM_LOW)
        alt_seq = alternating_sequence::type_id::create("alt_seq");
        alt_seq.start(sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
