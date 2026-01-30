// ============================================================================
// transaction_class.sv - UVM Transaction/Sequence Item
// ============================================================================
// Transactions (sequence items) represent stimulus/response at an abstract
// level. They extend uvm_sequence_item and contain:
// 1. Data fields (address, data, control signals, etc.)
// 2. Randomization constraints
// 3. Utility functions (copy, compare, print, etc.)
//
// Key Concepts:
// - Extend uvm_sequence_item
// - Use `uvm_object_utils macros
// - Add `uvm_field_* macros for automation
// - Use rand/randc for randomizable fields
// - Add constraints
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// BASIC TRANSACTION
// ============================================================================
class basic_transaction extends uvm_sequence_item;
    
    // Data fields
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit        we;  // write enable
    
    // Constructor
    function new(string name = "basic_transaction");
        super.new(name);
    endfunction
    
    // Minimal registration (no automation)
    `uvm_object_utils(basic_transaction)
    
endclass

// ============================================================================
// TRANSACTION WITH FIELD MACROS (recommended)
// ============================================================================
class auto_transaction extends uvm_sequence_item;
    
    // Data fields
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit        we;
    
    // Constructor
    function new(string name = "auto_transaction");
        super.new(name);
    endfunction
    
    // Registration WITH field automation
    `uvm_object_utils_begin(auto_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Field macros automatically provide:
    // - copy()
    // - compare()
    // - print()
    // - pack()/unpack()
    // - record()
    
endclass

// ============================================================================
// FULL-FEATURED TRANSACTION
// ============================================================================
typedef enum bit [1:0] {
    READ  = 2'b00,
    WRITE = 2'b01,
    RMW   = 2'b10,  // Read-Modify-Write
    IDLE  = 2'b11
} operation_e;

typedef enum bit [1:0] {
    OKAY  = 2'b00,
    ERROR = 2'b01,
    RETRY = 2'b10,
    BUSY  = 2'b11
} status_e;

class mem_transaction extends uvm_sequence_item;
    
    // ========================================
    // RANDOMIZABLE FIELDS (stimulus)
    // ========================================
    rand operation_e      op_type;
    rand bit [31:0]       addr;
    rand bit [31:0]       data;
    rand bit [3:0]        byte_enable;
    rand int unsigned     delay;  // cycles before starting
    
    // ========================================
    // NON-RANDOMIZABLE FIELDS (response)
    // ========================================
    status_e              status;
    bit [31:0]            read_data;
    time                  start_time;
    time                  end_time;
    
    // ========================================
    // CONSTRAINTS
    // ========================================
    
    // Address must be 4-byte aligned
    constraint addr_aligned_c {
        addr[1:0] == 2'b00;
    }
    
    // Address must be in valid range
    constraint addr_range_c {
        addr inside {[32'h0000_0000:32'h0000_FFFF]};
    }
    
    // Byte enable must be valid (no gaps)
    constraint valid_be_c {
        byte_enable inside {4'b0001, 4'b0011, 4'b0111, 4'b1111,
                           4'b0010, 4'b1100, 4'b1000};
    }
    
    // Reasonable delay
    constraint delay_c {
        delay inside {[0:10]};
    }
    
    // For WRITE/RMW, data should be non-zero (for interesting testing)
    constraint useful_data_c {
        (op_type inside {WRITE, RMW}) -> data != 0;
    }
    
    // ========================================
    // UVM AUTOMATION MACROS
    // ========================================
    `uvm_object_utils_begin(mem_transaction)
        `uvm_field_enum(operation_e, op_type, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(byte_enable, UVM_ALL_ON | UVM_BIN)
        `uvm_field_int(delay, UVM_ALL_ON)
        `uvm_field_enum(status_e, status, UVM_ALL_ON)
        `uvm_field_int(read_data, UVM_ALL_ON | UVM_HEX | UVM_NOCOMPARE)
        `uvm_field_int(start_time, UVM_ALL_ON | UVM_TIME | UVM_NOCOMPARE)
        `uvm_field_int(end_time, UVM_ALL_ON | UVM_TIME | UVM_NOCOMPARE)
    `uvm_object_utils_end
    
    // ========================================
    // CONSTRUCTOR
    // ========================================
    function new(string name = "mem_transaction");
        super.new(name);
    endfunction
    
    // ========================================
    // POST-RANDOMIZATION
    // ========================================
    function void post_randomize();
        // Align data based on byte_enable
        case (byte_enable)
            4'b0001: data = data & 32'h0000_00FF;
            4'b0011: data = data & 32'h0000_FFFF;
            4'b0111: data = data & 32'h00FF_FFFF;
            4'b1111: data = data & 32'hFFFF_FFFF;
            default: ;
        endcase
    endfunction
    
    // ========================================
    // CUSTOM CONVERT2STRING (optional)
    // ========================================
    function string convert2string();
        string s;
        s = $sformatf("%-8s addr=0x%08h", op_type.name(), addr);
        if (op_type == WRITE || op_type == RMW)
            s = {s, $sformatf(" wdata=0x%08h be=%04b", data, byte_enable)};
        if (status != OKAY)
            s = {s, $sformatf(" [%s]", status.name())};
        if (read_data != 0)
            s = {s, $sformatf(" rdata=0x%08h", read_data)};
        return s;
    endfunction
    
    // ========================================
    // CUSTOM COPY (if field macros aren't used)
    // ========================================
    // function void do_copy(uvm_object rhs);
    //     mem_transaction t;
    //     super.do_copy(rhs);
    //     $cast(t, rhs);
    //     op_type = t.op_type;
    //     addr = t.addr;
    //     // ... copy all fields
    // endfunction
    
    // ========================================
    // CUSTOM COMPARE (if field macros aren't used)
    // ========================================
    // function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    //     mem_transaction t;
    //     if (!super.do_compare(rhs, comparer)) return 0;
    //     $cast(t, rhs);
    //     return (op_type == t.op_type && addr == t.addr && ...);
    // endfunction
    
endclass

// ============================================================================
// TRANSACTION WITH NESTED OBJECTS
// ============================================================================
class header_t extends uvm_object;
    rand bit [7:0] src_id;
    rand bit [7:0] dest_id;
    rand bit [3:0] priority;
    
    `uvm_object_utils_begin(header_t)
        `uvm_field_int(src_id, UVM_ALL_ON)
        `uvm_field_int(dest_id, UVM_ALL_ON)
        `uvm_field_int(priority, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "header_t");
        super.new(name);
    endfunction
endclass

class packet_transaction extends uvm_sequence_item;
    rand header_t header;
    rand bit [7:0] payload[$];  // dynamic array
    rand int unsigned length;
    
    constraint length_c {
        length inside {[8:256]};
        payload.size() == length;
    }
    
    `uvm_object_utils_begin(packet_transaction)
        `uvm_field_object(header, UVM_ALL_ON)
        `uvm_field_queue_int(payload, UVM_ALL_ON)
        `uvm_field_int(length, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "packet_transaction");
        super.new(name);
        header = header_t::type_id::create("header");
    endfunction
endclass

// ============================================================================
// SIMPLE TEST
// ============================================================================
class transaction_test extends uvm_test;
    `uvm_component_utils(transaction_test)
    
    function new(string name = "transaction_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        mem_transaction tr1, tr2, tr_copy;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "\n=== Transaction Examples ===", UVM_LOW)
        
        // ========================================
        // Create and randomize
        // ========================================
        `uvm_info(get_type_name(), "\n--- Randomization ---", UVM_LOW)
        tr1 = mem_transaction::type_id::create("tr1");
        
        repeat(3) begin
            if (!tr1.randomize()) begin
                `uvm_error(get_type_name(), "Randomization failed")
            end
            `uvm_info(get_type_name(), tr1.convert2string(), UVM_LOW)
        end
        
        // ========================================
        // Inline constraints
        // ========================================
        `uvm_info(get_type_name(), "\n--- Inline Constraints ---", UVM_LOW)
        if (!tr1.randomize() with {
            op_type == WRITE;
            addr inside {[32'h1000:32'h1FFF]};
            data[31:24] == 8'hAA;
        }) begin
            `uvm_error(get_type_name(), "Constrained randomization failed")
        end
        `uvm_info(get_type_name(), tr1.convert2string(), UVM_LOW)
        
        // ========================================
        // Copy
        // ========================================
        `uvm_info(get_type_name(), "\n--- Copy ---", UVM_LOW)
        tr_copy = mem_transaction::type_id::create("tr_copy");
        tr_copy.copy(tr1);
        `uvm_info(get_type_name(), $sformatf("Original: %s", tr1.convert2string()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Copy    : %s", tr_copy.convert2string()), UVM_LOW)
        
        // ========================================
        // Compare
        // ========================================
        `uvm_info(get_type_name(), "\n--- Compare ---", UVM_LOW)
        if (tr1.compare(tr_copy)) begin
            `uvm_info(get_type_name(), "Transactions match!", UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), "Transactions don't match!")
        end
        
        // Modify and compare again
        tr_copy.addr = 32'hDEAD_BEEF;
        if (!tr1.compare(tr_copy)) begin
            `uvm_info(get_type_name(), "Transactions differ (as expected)", UVM_LOW)
        end
        
        // ========================================
        // Print
        // ========================================
        `uvm_info(get_type_name(), "\n--- Print ---", UVM_LOW)
        tr1.print();
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

// ============================================================================
// TOP MODULE
// ============================================================================
module top;
    initial begin
        run_test("transaction_test");
    end
endmodule
