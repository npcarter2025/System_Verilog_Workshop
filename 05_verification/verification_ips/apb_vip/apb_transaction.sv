// ============================================================================
// apb_transaction.sv - APB Transaction for VIP
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class apb_transaction extends uvm_sequence_item;
    
    typedef enum bit {
        APB_READ  = 1'b0,
        APB_WRITE = 1'b1
    } apb_direction_e;
    
    rand bit [31:0] addr;
    rand bit [31:0] wdata;
    rand apb_direction_e direction;
    bit [31:0] rdata;
    bit slverr;
    
    constraint addr_aligned_c {
        addr[1:0] == 2'b00;
    }
    
    `uvm_object_utils_begin(apb_transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(wdata, UVM_ALL_ON | UVM_HEX)
        `uvm_field_enum(apb_direction_e, direction, UVM_ALL_ON)
        `uvm_field_int(rdata, UVM_ALL_ON | UVM_HEX | UVM_NOCOMPARE)
        `uvm_field_int(slverr, UVM_ALL_ON | UVM_NOCOMPARE)
    `uvm_object_utils_end
    
    function new(string name = "apb_transaction");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("%s addr=0x%0h %s", 
                        direction.name(),
                        addr,
                        (direction == APB_WRITE) ? $sformatf("wdata=0x%0h", wdata) 
                                                  : $sformatf("rdata=0x%0h", rdata));
    endfunction
    
endclass
