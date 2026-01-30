// ============================================================================
// field_macros_example.sv - UVM Field Macro Reference
// ============================================================================
// Demonstrates all common UVM field automation macros and their flags
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

typedef enum {LOW, MEDIUM, HIGH} priority_e;

class config_object extends uvm_object;
    bit [7:0] id;
    string name;
    
    `uvm_object_utils_begin(config_object)
        `uvm_field_int(id, UVM_ALL_ON)
        `uvm_field_string(name, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "config_object");
        super.new(name);
    endfunction
endclass

class field_macro_example extends uvm_sequence_item;
    
    // Integer fields
    rand bit [31:0]       addr;
    rand bit [31:0]       data;
    rand bit [7:0]        id;
    
    // Enum
    rand priority_e       priority;
    
    // String
    string                tag;
    
    // Real
    real                  weight;
    
    // Object
    config_object         cfg;
    
    // Arrays
    rand bit [7:0]        payload[];
    rand bit [15:0]       fifo[$];
    
    // Static array
    bit [3:0]             control[4];
    
    `uvm_object_utils_begin(field_macro_example)
        // Basic integer field
        `uvm_field_int(addr, UVM_DEFAULT)
        
        // Integer with HEX display
        `uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
        
        // Integer excluded from compare
        `uvm_field_int(id, UVM_DEFAULT | UVM_NOCOMPARE)
        
        // Enum field
        `uvm_field_enum(priority_e, priority, UVM_DEFAULT)
        
        // String field
        `uvm_field_string(tag, UVM_DEFAULT)
        
        // Real field
        `uvm_field_real(weight, UVM_DEFAULT)
        
        // Object field
        `uvm_field_object(cfg, UVM_DEFAULT)
        
        // Dynamic array
        `uvm_field_array_int(payload, UVM_DEFAULT)
        
        // Queue
        `uvm_field_queue_int(fifo, UVM_DEFAULT)
        
        // Static array
        `uvm_field_sarray_int(control, UVM_DEFAULT)
    `uvm_object_utils_end
    
    function new(string name = "field_macro_example");
        super.new(name);
        cfg = config_object::type_id::create("cfg");
        payload = new[8];
        control = '{4'h1, 4'h2, 4'h3, 4'h4};
    endfunction
endclass

// Field macro flags:
// UVM_ALL_ON       - Enable all operations
// UVM_DEFAULT      - Standard set (copy, compare, print, record, pack)
// UVM_NOCOPY       - Exclude from copy()
// UVM_NOCOMPARE    - Exclude from compare()
// UVM_NOPRINT      - Exclude from print()
// UVM_NOPACK       - Exclude from pack()/unpack()
// UVM_REFERENCE    - Copy by reference, not value
// UVM_PHYSICAL     - Use physical representation
// UVM_ABSTRACT     - Use abstract representation
// UVM_READONLY     - Field is read-only
// UVM_HEX          - Print in hexadecimal
// UVM_DEC          - Print in decimal
// UVM_BIN          - Print in binary
// UVM_OCT          - Print in octal
// UVM_TIME         - Print as time

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(string name = "test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        field_macro_example obj1, obj2;
        
        phase.raise_objection(this);
        
        obj1 = field_macro_example::type_id::create("obj1");
        obj2 = field_macro_example::type_id::create("obj2");
        
        // Randomize
        assert(obj1.randomize());
        obj1.tag = "test_transaction";
        obj1.weight = 3.14;
        
        // Print
        `uvm_info("TEST", "\n=== Original Object ===", UVM_LOW)
        obj1.print();
        
        // Copy
        obj2.copy(obj1);
        `uvm_info("TEST", "\n=== Copied Object ===", UVM_LOW)
        obj2.print();
        
        // Compare
        if (obj1.compare(obj2))
            `uvm_info("TEST", "Objects match!", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
