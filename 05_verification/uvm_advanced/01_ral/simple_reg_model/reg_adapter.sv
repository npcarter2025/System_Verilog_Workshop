// ============================================================================
// reg_adapter.sv - Register Adapter for Bus Protocol
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class bus_transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit write;  // 1=write, 0=read
    
    `uvm_object_utils_begin(bus_transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(write, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "bus_transaction");
        super.new(name);
    endfunction
endclass

// Adapter converts between uvm_reg_bus_op and bus_transaction
class reg2bus_adapter extends uvm_reg_adapter;
    `uvm_object_utils(reg2bus_adapter)
    
    function new(string name = "reg2bus_adapter");
        super.new(name);
    endfunction
    
    // Convert register operation to bus transaction
    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        bus_transaction tr = bus_transaction::type_id::create("tr");
        
        tr.write = (rw.kind == UVM_WRITE);
        tr.addr = rw.addr;
        tr.data = rw.data;
        
        `uvm_info(get_type_name(), $sformatf("REG2BUS: %s addr=0x%0h data=0x%0h",
                  (tr.write ? "WRITE" : "READ"), tr.addr, tr.data), UVM_HIGH)
        
        return tr;
    endfunction
    
    // Convert bus transaction to register operation
    virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
        bus_transaction tr;
        
        if (!$cast(tr, bus_item)) begin
            `uvm_fatal(get_type_name(), "Failed to cast bus_item to bus_transaction")
        end
        
        rw.kind = tr.write ? UVM_WRITE : UVM_READ;
        rw.addr = tr.addr;
        rw.data = tr.data;
        rw.status = UVM_IS_OK;
        
        `uvm_info(get_type_name(), $sformatf("BUS2REG: %s addr=0x%0h data=0x%0h",
                  (rw.kind == UVM_WRITE ? "WRITE" : "READ"), rw.addr, rw.data), UVM_HIGH)
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        reg2bus_adapter adapter;
        uvm_reg_bus_op rw;
        bus_transaction tr;
        
        phase.raise_objection(this);
        
        adapter = reg2bus_adapter::type_id::create("adapter");
        
        // Test reg2bus
        rw.kind = UVM_WRITE;
        rw.addr = 32'h1000;
        rw.data = 32'hDEADBEEF;
        tr = bus_transaction'(adapter.reg2bus(rw));
        `uvm_info(get_type_name(), $sformatf("Created: %s", tr.convert2string()), UVM_LOW)
        
        // Test bus2reg
        tr.write = 0;
        tr.addr = 32'h2000;
        tr.data = 32'hCAFEBABE;
        adapter.bus2reg(tr, rw);
        `uvm_info(get_type_name(), $sformatf("Converted back: kind=%s addr=0x%0h data=0x%0h",
                  (rw.kind == UVM_WRITE ? "WRITE" : "READ"), rw.addr, rw.data), UVM_LOW)
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
