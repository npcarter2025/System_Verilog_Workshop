// ============================================================================
// reg_predictor.sv - Register Predictor (Auto-update)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class bus_transaction extends uvm_sequence_item;
    bit [31:0] addr;
    bit [31:0] data;
    bit write;
    `uvm_object_utils(bus_transaction)
    function new(string name = "bus_transaction");
        super.new(name);
    endfunction
endclass

class reg2bus_adapter extends uvm_reg_adapter;
    `uvm_object_utils(reg2bus_adapter)
    function new(string name = "reg2bus_adapter");
        super.new(name);
    endfunction
    
    function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        bus_transaction tr = bus_transaction::type_id::create("tr");
        tr.write = (rw.kind == UVM_WRITE);
        tr.addr = rw.addr;
        tr.data = rw.data;
        return tr;
    endfunction
    
    function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
        bus_transaction tr;
        $cast(tr, bus_item);
        rw.kind = tr.write ? UVM_WRITE : UVM_READ;
        rw.addr = tr.addr;
        rw.data = tr.data;
        rw.status = UVM_IS_OK;
    endfunction
endclass

class simple_reg extends uvm_reg;
    rand uvm_reg_field data;
    
    `uvm_object_utils(simple_reg)
    
    function new(string name = "simple_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction
    
    function void build();
        data = uvm_reg_field::type_id::create("data");
        data.configure(this, 32, 0, "RW", 0, 32'h0, 1, 1, 1);
    endfunction
endclass

class simple_reg_block extends uvm_reg_block;
    rand simple_reg my_reg;
    
    `uvm_object_utils(simple_reg_block)
    
    function new(string name = "simple_reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction
    
    function void build();
        default_map = create_map("default_map", 'h0, 4, UVM_LITTLE_ENDIAN);
        
        my_reg = simple_reg::type_id::create("my_reg");
        my_reg.configure(this);
        my_reg.build();
        
        default_map.add_reg(my_reg, 'h0, "RW");
        lock_model();
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    simple_reg_block regmodel;
    reg2bus_adapter adapter;
    uvm_reg_predictor#(bus_transaction) predictor;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        // Create register model
        regmodel = simple_reg_block::type_id::create("regmodel");
        regmodel.build();
        
        // Create adapter
        adapter = reg2bus_adapter::type_id::create("adapter");
        
        // Create predictor
        predictor = uvm_reg_predictor#(bus_transaction)::type_id::create("predictor", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        // Connect predictor to register model
        predictor.map = regmodel.default_map;
        predictor.adapter = adapter;
        
        // In real testbench, monitor's analysis port would connect to predictor
        // monitor.ap.connect(predictor.bus_in);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Predictor keeps register model in sync with DUT", UVM_LOW)
        `uvm_info(get_type_name(), "Monitor transactions -> Predictor -> Updates regmodel", UVM_LOW)
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
