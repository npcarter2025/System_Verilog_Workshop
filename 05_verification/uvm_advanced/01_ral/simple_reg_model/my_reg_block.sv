// ============================================================================
// my_reg_block.sv - Simple Register Model (RAL)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Individual register
class control_reg extends uvm_reg;
    rand uvm_reg_field enable;
    rand uvm_reg_field mode;
    rand uvm_reg_field reserved;
    
    function new(string name = "control_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        enable = uvm_reg_field::type_id::create("enable");
        mode = uvm_reg_field::type_id::create("mode");
        reserved = uvm_reg_field::type_id::create("reserved");
        
        // configure(parent, size, lsb_pos, access, volatile, reset, has_reset, is_rand, individually_accessible)
        enable.configure(this, 1, 0, "RW", 0, 1'h0, 1, 1, 1);
        mode.configure(this, 3, 1, "RW", 0, 3'h0, 1, 1, 1);
        reserved.configure(this, 28, 4, "RO", 0, 28'h0, 1, 0, 1);
    endfunction
endclass

class status_reg extends uvm_reg;
    uvm_reg_field busy;
    uvm_reg_field error;
    uvm_reg_field done;
    
    function new(string name = "status_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        busy = uvm_reg_field::type_id::create("busy");
        error = uvm_reg_field::type_id::create("error");
        done = uvm_reg_field::type_id::create("done");
        
        busy.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
        error.configure(this, 1, 1, "RO", 0, 1'h0, 1, 0, 1);
        done.configure(this, 1, 2, "RO", 0, 1'h0, 1, 0, 1);
    endfunction
endclass

class data_reg extends uvm_reg;
    rand uvm_reg_field data;
    
    function new(string name = "data_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        data = uvm_reg_field::type_id::create("data");
        data.configure(this, 32, 0, "RW", 0, 32'h0, 1, 1, 1);
    endfunction
endclass

// Register block
class my_reg_block extends uvm_reg_block;
    rand control_reg ctrl_reg;
    rand status_reg stat_reg;
    rand data_reg data_reg_0;
    rand data_reg data_reg_1;
    
    function new(string name = "my_reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        // Create address map
        default_map = create_map("default_map", 'h0, 4, UVM_LITTLE_ENDIAN);
        
        // Create registers
        ctrl_reg = control_reg::type_id::create("ctrl_reg");
        ctrl_reg.configure(this);
        ctrl_reg.build();
        
        stat_reg = status_reg::type_id::create("stat_reg");
        stat_reg.configure(this);
        stat_reg.build();
        
        data_reg_0 = data_reg::type_id::create("data_reg_0");
        data_reg_0.configure(this);
        data_reg_0.build();
        
        data_reg_1 = data_reg::type_id::create("data_reg_1");
        data_reg_1.configure(this);
        data_reg_1.build();
        
        // Add registers to map (address offset in bytes)
        default_map.add_reg(ctrl_reg, 'h0, "RW");
        default_map.add_reg(stat_reg, 'h4, "RO");
        default_map.add_reg(data_reg_0, 'h8, "RW");
        default_map.add_reg(data_reg_1, 'hC, "RW");
        
        lock_model();
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    my_reg_block regmodel;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        regmodel = my_reg_block::type_id::create("regmodel");
        regmodel.build();
        
        `uvm_info(get_type_name(), "Register model built", UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        uvm_status_e status;
        uvm_reg_data_t value;
        
        phase.raise_objection(this);
        
        // Example register operations (would normally go through adapter)
        `uvm_info(get_type_name(), "=== Register Model Example ===", UVM_LOW)
        
        // Set desired value
        regmodel.ctrl_reg.enable.set(1'b1);
        regmodel.ctrl_reg.mode.set(3'b101);
        
        `uvm_info(get_type_name(), $sformatf("Control register value: 0x%0h", 
                  regmodel.ctrl_reg.get()), UVM_LOW)
        
        // Print register model
        regmodel.print();
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
