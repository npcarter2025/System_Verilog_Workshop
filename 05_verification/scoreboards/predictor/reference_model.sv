// ============================================================================
// reference_model.sv - Reference Model for Functional Verification
// ============================================================================
// A reference model is a high-level, functionally accurate representation
// of the DUT behavior. It generates expected outputs for given inputs.
// ============================================================================

// ============================================================================
// Transaction Classes
// ============================================================================
class alu_transaction;
    rand bit [31:0] operand_a;
    rand bit [31:0] operand_b;
    rand bit [3:0] opcode;
    bit [31:0] result;
    bit zero_flag;
    bit carry_flag;
    bit overflow_flag;
    time timestamp;
    
    typedef enum bit [3:0] {
        ADD  = 4'h0,
        SUB  = 4'h1,
        AND  = 4'h2,
        OR   = 4'h3,
        XOR  = 4'h4,
        SLL  = 4'h5,  // Shift left logical
        SRL  = 4'h6,  // Shift right logical
        SRA  = 4'h7,  // Shift right arithmetic
        MUL  = 4'h8,
        DIV  = 4'h9
    } opcode_e;
    
    function new();
        timestamp = $time;
    endfunction
    
    function string convert2string();
        return $sformatf("[%0t] ALU: a=0x%08h, b=0x%08h, op=%0d → result=0x%08h [Z=%0b C=%0b V=%0b]",
                        timestamp, operand_a, operand_b, opcode, result, 
                        zero_flag, carry_flag, overflow_flag);
    endfunction
endclass

// ============================================================================
// Simple Reference Model: ALU
// ============================================================================
class alu_reference_model;
    string name;
    
    function new(string model_name = "ALU_REF_MODEL");
        name = model_name;
    endfunction
    
    // Compute expected result
    function void compute(alu_transaction tr);
        bit [32:0] temp_result;  // Extra bit for carry
        bit sign_a, sign_b, sign_r;
        
        $display("[%s] Computing: a=0x%08h op=%0d b=0x%08h", 
                name, tr.operand_a, tr.opcode, tr.operand_b);
        
        case (tr.opcode)
            alu_transaction::ADD: begin
                temp_result = {1'b0, tr.operand_a} + {1'b0, tr.operand_b};
                tr.result = temp_result[31:0];
                tr.carry_flag = temp_result[32];
                
                // Overflow: operands have same sign, result has different sign
                sign_a = tr.operand_a[31];
                sign_b = tr.operand_b[31];
                sign_r = tr.result[31];
                tr.overflow_flag = (sign_a == sign_b) && (sign_a != sign_r);
            end
            
            alu_transaction::SUB: begin
                temp_result = {1'b0, tr.operand_a} - {1'b0, tr.operand_b};
                tr.result = temp_result[31:0];
                tr.carry_flag = temp_result[32];
                
                sign_a = tr.operand_a[31];
                sign_b = tr.operand_b[31];
                sign_r = tr.result[31];
                tr.overflow_flag = (sign_a != sign_b) && (sign_a != sign_r);
            end
            
            alu_transaction::AND: begin
                tr.result = tr.operand_a & tr.operand_b;
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::OR: begin
                tr.result = tr.operand_a | tr.operand_b;
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::XOR: begin
                tr.result = tr.operand_a ^ tr.operand_b;
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::SLL: begin
                tr.result = tr.operand_a << tr.operand_b[4:0];
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::SRL: begin
                tr.result = tr.operand_a >> tr.operand_b[4:0];
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::SRA: begin
                tr.result = $signed(tr.operand_a) >>> tr.operand_b[4:0];
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
            
            alu_transaction::MUL: begin
                bit [63:0] mul_result = tr.operand_a * tr.operand_b;
                tr.result = mul_result[31:0];
                tr.carry_flag = (mul_result[63:32] != 0);
                tr.overflow_flag = 0;
            end
            
            alu_transaction::DIV: begin
                if (tr.operand_b == 0) begin
                    tr.result = 32'hFFFF_FFFF;  // Error value
                    tr.overflow_flag = 1;
                end else begin
                    tr.result = tr.operand_a / tr.operand_b;
                    tr.overflow_flag = 0;
                end
                tr.carry_flag = 0;
            end
            
            default: begin
                $error("[%s] Unknown opcode: %0d", name, tr.opcode);
                tr.result = 32'h0;
                tr.carry_flag = 0;
                tr.overflow_flag = 0;
            end
        endcase
        
        // Zero flag
        tr.zero_flag = (tr.result == 32'h0);
        
        $display("[%s] Result: 0x%08h [Z=%0b C=%0b V=%0b]", 
                name, tr.result, tr.zero_flag, tr.carry_flag, tr.overflow_flag);
    endfunction
endclass

// ============================================================================
// Memory Reference Model
// ============================================================================
class memory_transaction;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit write;  // 1=write, 0=read
    rand bit [3:0] byte_enable;
    
    constraint addr_aligned_c {
        addr[1:0] == 2'b00;
    }
    
    function string convert2string();
        return $sformatf("%s addr=0x%08h data=0x%08h be=%04b",
                        write ? "WRITE" : "READ", addr, data, byte_enable);
    endfunction
endclass

class memory_reference_model;
    bit [7:0] memory[bit [31:0]];  // Sparse memory model
    string name;
    
    function new(string model_name = "MEM_REF_MODEL");
        name = model_name;
    endfunction
    
    // Process transaction
    function void process(memory_transaction tr);
        if (tr.write) begin
            write_memory(tr.addr, tr.data, tr.byte_enable);
        end else begin
            tr.data = read_memory(tr.addr, tr.byte_enable);
        end
    endfunction
    
    // Write to memory
    function void write_memory(bit [31:0] addr, bit [31:0] data, bit [3:0] be);
        $display("[%s] Write addr=0x%08h data=0x%08h be=%04b", 
                name, addr, data, be);
        
        // Write byte-by-byte based on byte enable
        if (be[0]) memory[addr + 0] = data[7:0];
        if (be[1]) memory[addr + 1] = data[15:8];
        if (be[2]) memory[addr + 2] = data[23:16];
        if (be[3]) memory[addr + 3] = data[31:24];
    endfunction
    
    // Read from memory
    function bit [31:0] read_memory(bit [31:0] addr, bit [3:0] be);
        bit [31:0] data = 32'h0;
        
        // Read byte-by-byte, return 0 for uninitialized
        data[7:0]   = be[0] ? (memory.exists(addr + 0) ? memory[addr + 0] : 8'h00) : 8'h00;
        data[15:8]  = be[1] ? (memory.exists(addr + 1) ? memory[addr + 1] : 8'h00) : 8'h00;
        data[23:16] = be[2] ? (memory.exists(addr + 2) ? memory[addr + 2] : 8'h00) : 8'h00;
        data[31:24] = be[3] ? (memory.exists(addr + 3) ? memory[addr + 3] : 8'h00) : 8'h00;
        
        $display("[%s] Read addr=0x%08h data=0x%08h be=%04b", 
                name, addr, data, be);
        
        return data;
    endfunction
    
    // Load memory from file
    function void load_from_file(string filename);
        int fd;
        bit [31:0] addr, data;
        
        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $error("[%s] Failed to open %s", name, filename);
            return;
        end
        
        while (!$feof(fd)) begin
            if ($fscanf(fd, "%h %h", addr, data) == 2) begin
                write_memory(addr, data, 4'hF);
            end
        end
        
        $fclose(fd);
        $display("[%s] Loaded memory from %s", name, filename);
    endfunction
    
    // Dump memory to file
    function void dump_to_file(string filename);
        int fd;
        bit [31:0] addr;
        
        fd = $fopen(filename, "w");
        if (fd == 0) begin
            $error("[%s] Failed to open %s", name, filename);
            return;
        end
        
        if (memory.first(addr)) begin
            do begin
                $fdisplay(fd, "%08h %02h", addr, memory[addr]);
            end while (memory.next(addr));
        end
        
        $fclose(fd);
        $display("[%s] Dumped memory to %s", name, filename);
    endfunction
endclass

// ============================================================================
// FIFO Reference Model
// ============================================================================
class fifo_transaction;
    rand bit [7:0] data;
    rand bit push;
    rand bit pop;
    
    function string convert2string();
        string op = push ? "PUSH" : (pop ? "POP" : "IDLE");
        return $sformatf("%s data=0x%02h", op, data);
    endfunction
endclass

class fifo_reference_model #(parameter DEPTH = 16);
    bit [7:0] queue[$];
    int max_depth;
    string name;
    
    function new(string model_name = "FIFO_REF_MODEL");
        name = model_name;
        max_depth = DEPTH;
    endfunction
    
    function void process(fifo_transaction tr);
        // Push
        if (tr.push && !is_full()) begin
            queue.push_back(tr.data);
            $display("[%s] Pushed 0x%02h (depth=%0d)", name, tr.data, queue.size());
        end else if (tr.push) begin
            $warning("[%s] Push ignored (FIFO full)", name);
        end
        
        // Pop
        if (tr.pop && !is_empty()) begin
            tr.data = queue.pop_front();
            $display("[%s] Popped 0x%02h (depth=%0d)", name, tr.data, queue.size());
        end else if (tr.pop) begin
            $warning("[%s] Pop ignored (FIFO empty)", name);
            tr.data = 8'h00;
        end
    endfunction
    
    function bit is_full();
        return (queue.size() >= max_depth);
    endfunction
    
    function bit is_empty();
        return (queue.size() == 0);
    endfunction
    
    function int get_count();
        return queue.size();
    endfunction
    
    function void reset();
        queue.delete();
        $display("[%s] Reset", name);
    endfunction
endclass

// ============================================================================
// Testbench
// ============================================================================
module reference_model_tb;
    
    initial begin
        alu_reference_model alu_model;
        memory_reference_model mem_model;
        fifo_reference_model #(16) fifo_model;
        
        alu_transaction alu_tr;
        memory_transaction mem_tr;
        fifo_transaction fifo_tr;
        
        $display("\n=== Reference Model Examples ===\n");
        
        // Test ALU Reference Model
        $display("--- ALU Reference Model ---");
        alu_model = new();
        
        // Test ADD
        alu_tr = new();
        alu_tr.operand_a = 32'h00000005;
        alu_tr.operand_b = 32'h00000003;
        alu_tr.opcode = alu_transaction::ADD;
        alu_model.compute(alu_tr);
        alu_tr.display();
        
        // Test SUB with overflow
        alu_tr = new();
        alu_tr.operand_a = 32'h80000000;
        alu_tr.operand_b = 32'h00000001;
        alu_tr.opcode = alu_transaction::SUB;
        alu_model.compute(alu_tr);
        alu_tr.display();
        
        // Test MUL
        alu_tr = new();
        alu_tr.operand_a = 32'h00001000;
        alu_tr.operand_b = 32'h00001000;
        alu_tr.opcode = alu_transaction::MUL;
        alu_model.compute(alu_tr);
        alu_tr.display();
        
        // Test Memory Reference Model
        $display("\n--- Memory Reference Model ---");
        mem_model = new();
        
        // Write
        mem_tr = new();
        mem_tr.addr = 32'h00001000;
        mem_tr.data = 32'hDEADBEEF;
        mem_tr.write = 1;
        mem_tr.byte_enable = 4'hF;
        mem_model.process(mem_tr);
        
        // Read back
        mem_tr = new();
        mem_tr.addr = 32'h00001000;
        mem_tr.write = 0;
        mem_tr.byte_enable = 4'hF;
        mem_model.process(mem_tr);
        $display("Read back: 0x%08h", mem_tr.data);
        
        // Partial write (byte enables)
        mem_tr = new();
        mem_tr.addr = 32'h00001000;
        mem_tr.data = 32'hCAFEBABE;
        mem_tr.write = 1;
        mem_tr.byte_enable = 4'b0011;  // Only lower 2 bytes
        mem_model.process(mem_tr);
        
        // Read back
        mem_tr = new();
        mem_tr.addr = 32'h00001000;
        mem_tr.write = 0;
        mem_tr.byte_enable = 4'hF;
        mem_model.process(mem_tr);
        $display("After partial write: 0x%08h", mem_tr.data);
        
        // Test FIFO Reference Model
        $display("\n--- FIFO Reference Model ---");
        fifo_model = new();
        
        // Push some data
        for (int i = 0; i < 5; i++) begin
            fifo_tr = new();
            fifo_tr.push = 1;
            fifo_tr.pop = 0;
            fifo_tr.data = 8'(i * 10);
            fifo_model.process(fifo_tr);
        end
        
        $display("FIFO count: %0d", fifo_model.get_count());
        
        // Pop data
        for (int i = 0; i < 3; i++) begin
            fifo_tr = new();
            fifo_tr.push = 0;
            fifo_tr.pop = 1;
            fifo_model.process(fifo_tr);
            $display("Popped value: 0x%02h", fifo_tr.data);
        end
        
        $display("FIFO count after pops: %0d", fifo_model.get_count());
        
        $display("\n=== Reference Model Tests Complete ===\n");
        $finish;
    end
    
endmodule

/*
 * REFERENCE MODEL:
 * 
 * PURPOSE:
 * - Generate expected outputs for given inputs
 * - Functional verification (not timing)
 * - High-level, behavioral model
 * - "Golden" reference for comparison
 * 
 * CHARACTERISTICS:
 * - Functionally accurate
 * - Not cycle-accurate
 * - High-level abstraction
 * - Easy to understand/maintain
 * - Fast execution
 * 
 * TYPES OF REFERENCE MODELS:
 * 
 * 1. Behavioral:
 *    - High-level algorithm
 *    - No timing
 *    - Pure function
 * 
 * 2. Transaction-Level:
 *    - Processes transactions
 *    - No pin wiggling
 *    - TLM style
 * 
 * 3. Cycle-Approximate:
 *    - Some timing
 *    - Not exact cycles
 *    - Performance model
 * 
 * 4. Software Model:
 *    - C/C++/Python
 *    - DPI-C interface
 *    - Reuse software
 * 
 * IMPLEMENTATION APPROACHES:
 * 
 * 1. Inline Functions:
 *    function compute(input, output);
 *      output = f(input);
 *    endfunction
 * 
 * 2. Class-Based:
 *    class ref_model;
 *      function process(tr);
 *      endfunction
 *    endclass
 * 
 * 3. External (DPI-C):
 *    import "DPI-C" function compute();
 * 
 * BEST PRACTICES:
 * 1. Keep it simple
 * 2. Functionally correct
 * 3. Well-documented
 * 4. Independently testable
 * 5. Match DUT spec
 * 6. Handle edge cases
 * 
 * WHAT TO MODEL:
 * ✓ Arithmetic operations
 * ✓ Memory behavior
 * ✓ State machines
 * ✓ FIFOs/queues
 * ✓ Protocol behavior
 * ✓ Data transformations
 * 
 * WHAT NOT TO MODEL:
 * ✗ Exact timing
 * ✗ Clock domains
 * ✗ Physical interfaces
 * ✗ Power states (usually)
 * ✗ Manufacturing defects
 * 
 * VERIFICATION FLOW:
 * 1. Input → DUT → Actual Output
 * 2. Input → Ref Model → Expected Output
 * 3. Compare: Actual vs Expected
 * 4. Report: Pass/Fail
 * 
 * ACCURACY LEVELS:
 * 
 * Functional Only:
 * - Correct result
 * - No timing
 * - Fastest
 * 
 * Cycle-Approximate:
 * - Correct result
 * - Approximate timing
 * - Medium speed
 * 
 * Cycle-Accurate:
 * - Correct result
 * - Exact timing
 * - Slowest
 * - Often unnecessary
 * 
 * COMMON MODELS:
 * - ALU: Arithmetic/logic
 * - Memory: Read/write
 * - FIFO: Push/pop
 * - Cache: Hit/miss
 * - CPU: Instruction execution
 * - DSP: Signal processing
 * 
 * VALIDATION:
 * - Test ref model independently
 * - Known input/output pairs
 * - Corner cases
 * - Compare against spec
 * - Review with designers
 * 
 * MAINTENANCE:
 * - Update with DUT changes
 * - Version control
 * - Document assumptions
 * - Track spec changes
 * 
 * ADVANTAGES:
 * + Fast execution
 * + Easy to understand
 * + Independent of RTL
 * + Reusable
 * + Can be software
 * 
 * DISADVANTAGES:
 * - No timing info
 * - Another thing to maintain
 * - Can diverge from DUT
 * - May miss RTL bugs
 * 
 * INTEGRATION:
 * - Used by predictor scoreboard
 * - Feeds expected values
 * - Can be standalone
 * - Often in verification package
 * 
 * LANGUAGES:
 * - SystemVerilog: Native integration
 * - C/C++: Via DPI-C
 * - Python: Via DPI or socket
 * - MATLAB: Via co-simulation
 * 
 * TIPS:
 * ✓ Start simple
 * ✓ Add complexity as needed
 * ✓ Test independently
 * ✓ Document thoroughly
 * ✓ Keep synchronized with spec
 * ✓ Handle all opcodes/modes
 * ✓ Consider performance
 */
