// ============================================================================
// apb_read_seq.sv - APB Read Sequence
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class apb_read_seq extends uvm_sequence#(apb_transaction);
    `uvm_object_utils(apb_read_seq)
    
    rand bit [31:0] addr;
    bit [31:0] rdata;
    
    function new(string name = "apb_read_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction tr;
        
        tr = apb_transaction::type_id::create("tr");
        start_item(tr);
        tr.direction = apb_transaction::APB_READ;
        tr.addr = addr;
        finish_item(tr);
        
        // Get response
        get_response(tr);
        rdata = tr.rdata;
        
        `uvm_info(get_type_name(), $sformatf("APB Read: addr=0x%0h rdata=0x%0h", addr, rdata), UVM_MEDIUM)
    endtask
    
endclass
