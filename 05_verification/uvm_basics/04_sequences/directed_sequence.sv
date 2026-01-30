// ============================================================================
// directed_sequence.sv - Directed (Non-random) Sequences
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [15:0] addr;
    rand bit [31:0] data;
    rand bit        wr_rd;
    
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(wr_rd, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Corner case sequence
class corner_case_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(corner_case_sequence)
    
    function new(string name = "corner_case_sequence");
        super.new(name);
    endfunction
    
    task body();
        transaction tr;
        
        // Test case 1: Address 0
        tr = transaction::type_id::create("addr_zero");
        start_item(tr);
        tr.addr = 16'h0000;
        tr.data = 32'hDEADBEEF;
        tr.wr_rd = 1'b1;
        finish_item(tr);
        
        // Test case 2: Max address
        tr = transaction::type_id::create("addr_max");
        start_item(tr);
        tr.addr = 16'hFFFF;
        tr.data = 32'hCAFEBABE;
        tr.wr_rd = 1'b1;
        finish_item(tr);
        
        // Test case 3: All zeros
        tr = transaction::type_id::create("all_zero");
        start_item(tr);
        tr.addr = 16'h0000;
        tr.data = 32'h00000000;
        tr.wr_rd = 1'b1;
        finish_item(tr);
        
        // Test case 4: All ones
        tr = transaction::type_id::create("all_ones");
        start_item(tr);
        tr.addr = 16'hFFFF;
        tr.data = 32'hFFFFFFFF;
        tr.wr_rd = 1'b1;
        finish_item(tr);
    endtask
endclass

// Walking pattern sequence
class walking_pattern_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(walking_pattern_sequence)
    
    function new(string name = "walking_pattern_sequence");
        super.new(name);
    endfunction
    
    task body();
        transaction tr;
        
        // Walking 1s
        for (int i = 0; i < 32; i++) begin
            tr = transaction::type_id::create($sformatf("walk1_%0d", i));
            start_item(tr);
            tr.addr = 16'h1000 + i;
            tr.data = (32'h1 << i);
            tr.wr_rd = 1'b1;
            finish_item(tr);
        end
        
        // Walking 0s
        for (int i = 0; i < 32; i++) begin
            tr = transaction::type_id::create($sformatf("walk0_%0d", i));
            start_item(tr);
            tr.addr = 16'h2000 + i;
            tr.data = ~(32'h1 << i);
            tr.wr_rd = 1'b1;
            finish_item(tr);
        end
    endtask
endclass

// Register access sequence
class register_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(register_sequence)
    
    bit [15:0] base_addr = 16'h1000;
    
    function new(string name = "register_sequence");
        super.new(name);
    endfunction
    
    task write_reg(bit [7:0] offset, bit [31:0] data);
        transaction tr = transaction::type_id::create("write_tr");
        start_item(tr);
        tr.addr = base_addr + offset;
        tr.data = data;
        tr.wr_rd = 1'b1;
        finish_item(tr);
    endtask
    
    task read_reg(bit [7:0] offset);
        transaction tr = transaction::type_id::create("read_tr");
        start_item(tr);
        tr.addr = base_addr + offset;
        tr.data = 32'h0;
        tr.wr_rd = 1'b0;
        finish_item(tr);
    endtask
    
    task body();
        // Write configuration registers
        write_reg(8'h00, 32'h0000_0001);  // Enable
        write_reg(8'h04, 32'h0000_00FF);  // Config
        write_reg(8'h08, 32'h1234_5678);  // Data
        
        // Read back
        read_reg(8'h00);
        read_reg(8'h04);
        read_reg(8'h08);
        
        // Write command
        write_reg(8'h0C, 32'h8000_0000);  // Start command
    endtask
endclass

typedef uvm_sequencer#(transaction) my_sequencer;

class test extends uvm_test;
    `uvm_component_utils(test)
    my_sequencer sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = my_sequencer::type_id::create("sequencer", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        corner_case_sequence corner_seq;
        walking_pattern_sequence walk_seq;
        register_sequence reg_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "Running corner case sequence", UVM_LOW)
        corner_seq = corner_case_sequence::type_id::create("corner_seq");
        corner_seq.start(sequencer);
        
        `uvm_info("TEST", "Running walking pattern sequence", UVM_LOW)
        walk_seq = walking_pattern_sequence::type_id::create("walk_seq");
        walk_seq.start(sequencer);
        
        `uvm_info("TEST", "Running register sequence", UVM_LOW)
        reg_seq = register_sequence::type_id::create("reg_seq");
        reg_seq.start(sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
