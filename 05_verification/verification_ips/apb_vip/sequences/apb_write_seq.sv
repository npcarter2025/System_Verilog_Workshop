// ============================================================================
// apb_write_seq.sv - APB Write Sequence
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class apb_write_seq extends uvm_sequence#(apb_transaction);
    `uvm_object_utils(apb_write_seq)
    
    rand bit [31:0] addr;
    rand bit [31:0] data;
    
    function new(string name = "apb_write_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction tr;
        
        tr = apb_transaction::type_id::create("tr");
        start_item(tr);
        tr.direction = apb_transaction::APB_WRITE;
        tr.addr = addr;
        tr.wdata = data;
        finish_item(tr);
        
        `uvm_info(get_type_name(), $sformatf("APB Write: addr=0x%0h data=0x%0h", addr, data), UVM_MEDIUM)
    endtask
    
endclass
