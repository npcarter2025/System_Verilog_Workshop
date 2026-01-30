// ============================================================================
// alu_transaction.sv - ALU Transaction Class
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

typedef enum bit [2:0] {
    ADD  = 3'b000,
    SUB  = 3'b001,
    AND  = 3'b010,
    OR   = 3'b011,
    XOR  = 3'b100,
    SLL  = 3'b101,
    SRL  = 3'b110,
    SRA  = 3'b111
} alu_op_e;

class alu_transaction #(int WIDTH = 8) extends uvm_sequence_item;
    
    rand bit [WIDTH-1:0] a;
    rand bit [WIDTH-1:0] b;
    rand alu_op_e op;
    bit [WIDTH-1:0] result;
    
    `uvm_object_param_utils_begin(alu_transaction#(WIDTH))
        `uvm_field_int(a, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(b, UVM_ALL_ON | UVM_HEX)
        `uvm_field_enum(alu_op_e, op, UVM_ALL_ON)
        `uvm_field_int(result, UVM_ALL_ON | UVM_HEX | UVM_NOCOMPARE)
    `uvm_object_utils_end
    
    function new(string name = "alu_transaction");
        super.new(name);
    endfunction
    
    function bit [WIDTH-1:0] compute_expected();
        case (op)
            ADD: return a + b;
            SUB: return a - b;
            AND: return a & b;
            OR:  return a | b;
            XOR: return a ^ b;
            SLL: return a << b[2:0];
            SRL: return a >> b[2:0];
            SRA: return $signed(a) >>> b[2:0];
        endcase
    endfunction
    
endclass
