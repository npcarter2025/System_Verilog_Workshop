// ============================================================================
// predictor_scoreboard.sv - Predictor-Based Scoreboard
// ============================================================================
// Combines a reference model with scoreboard checking
// Reference model predicts expected outputs, scoreboard compares
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// Transaction Class
// ============================================================================
class pred_transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] wdata;
    bit [31:0] rdata;
    rand bit write;
    rand bit [3:0] byte_en;
    time timestamp;
    
    `uvm_object_utils_begin(pred_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(wdata, UVM_ALL_ON)
        `uvm_field_int(rdata, UVM_ALL_ON)
        `uvm_field_int(write, UVM_ALL_ON)
        `uvm_field_int(byte_en, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "pred_transaction");
        super.new(name);
        timestamp = $time;
    endfunction
endclass

// ============================================================================
// Simple Memory Reference Model
// ============================================================================
class memory_predictor;
    bit [7:0] memory[bit [31:0]];
    string name;
    
    function new(string predictor_name = "MEM_PREDICTOR");
        name = predictor_name;
    endfunction
    
    // Predict response based on request
    function void predict(pred_transaction tr);
        if (tr.write) begin
            write_memory(tr.addr, tr.wdata, tr.byte_en);
            `uvm_info(name, $sformatf("Predicted WRITE: addr=0x%08h data=0x%08h", 
                                     tr.addr, tr.wdata), UVM_HIGH)
        end else begin
            tr.rdata = read_memory(tr.addr, tr.byte_en);
            `uvm_info(name, $sformatf("Predicted READ: addr=0x%08h data=0x%08h", 
                                     tr.addr, tr.rdata), UVM_HIGH)
        end
    endfunction
    
    function void write_memory(bit [31:0] addr, bit [31:0] data, bit [3:0] be);
        if (be[0]) memory[addr + 0] = data[7:0];
        if (be[1]) memory[addr + 1] = data[15:8];
        if (be[2]) memory[addr + 2] = data[23:16];
        if (be[3]) memory[addr + 3] = data[31:24];
    endfunction
    
    function bit [31:0] read_memory(bit [31:0] addr, bit [3:0] be);
        bit [31:0] data = 32'h0;
        data[7:0]   = be[0] ? (memory.exists(addr+0) ? memory[addr+0] : 8'h00) : 8'h00;
        data[15:8]  = be[1] ? (memory.exists(addr+1) ? memory[addr+1] : 8'h00) : 8'h00;
        data[23:16] = be[2] ? (memory.exists(addr+2) ? memory[addr+2] : 8'h00) : 8'h00;
        data[31:24] = be[3] ? (memory.exists(addr+3) ? memory[addr+3] : 8'h00) : 8'h00;
        return data;
    endfunction
    
    function void reset();
        memory.delete();
        `uvm_info(name, "Memory reset", UVM_MEDIUM)
    endfunction
endclass

// ============================================================================
// Predictor Scoreboard (UVM Style)
// ============================================================================
class predictor_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(predictor_scoreboard)
    
    // Analysis ports
    uvm_analysis_imp_request #(pred_transaction, predictor_scoreboard) request_export;
    uvm_analysis_imp_response #(pred_transaction, predictor_scoreboard) response_export;
    
    // Reference model/predictor
    memory_predictor predictor;
    
    // Expected queue (for reads)
    pred_transaction expected_queue[$];
    
    // Statistics
    int match_count;
    int mismatch_count;
    int write_count;
    int read_count;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        predictor = new("PREDICTOR");
        match_count = 0;
        mismatch_count = 0;
        write_count = 0;
        read_count = 0;
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        request_export = new("request_export", this);
        response_export = new("response_export", this);
    endfunction
    
    // Receive request, generate expected
    function void write_request(pred_transaction tr);
        pred_transaction exp_tr;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Received request: %s addr=0x%08h", 
                          tr.write ? "WRITE" : "READ", tr.addr),
                 UVM_MEDIUM)
        
        // Clone transaction
        $cast(exp_tr, tr.clone());
        
        // Use predictor to generate expected
        predictor.predict(exp_tr);
        
        if (exp_tr.write) begin
            write_count++;
            // Writes don't need response checking
        end else begin
            read_count++;
            // Store expected for read response
            expected_queue.push_back(exp_tr);
            `uvm_info(get_type_name(), 
                     $sformatf("Queued expected read data: 0x%08h (queue size=%0d)", 
                              exp_tr.rdata, expected_queue.size()),
                     UVM_HIGH)
        end
    endfunction
    
    // Receive response, compare with expected
    function void write_response(pred_transaction tr);
        pred_transaction exp_tr;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Received response: addr=0x%08h data=0x%08h", 
                          tr.addr, tr.rdata),
                 UVM_MEDIUM)
        
        // Only check read responses
        if (!tr.write) begin
            if (expected_queue.size() == 0) begin
                `uvm_error(get_type_name(), "No expected read response!")
                mismatch_count++;
                return;
            end
            
            exp_tr = expected_queue.pop_front();
            
            // Compare
            if (exp_tr.rdata == tr.rdata) begin
                `uvm_info(get_type_name(), 
                         $sformatf("PASS: Read data matched at addr 0x%08h: 0x%08h", 
                                  tr.addr, tr.rdata),
                         UVM_MEDIUM)
                match_count++;
            end else begin
                `uvm_error(get_type_name(), 
                          $sformatf("FAIL: Read data mismatch at addr 0x%08h", tr.addr))
                `uvm_info(get_type_name(), 
                         $sformatf("Expected: 0x%08h", exp_tr.rdata),
                         UVM_NONE)
                `uvm_info(get_type_name(), 
                         $sformatf("Actual:   0x%08h", tr.rdata),
                         UVM_NONE)
                mismatch_count++;
            end
        end
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "\n========================================", UVM_LOW)
        `uvm_info(get_type_name(), "  PREDICTOR SCOREBOARD REPORT", UVM_LOW)
        `uvm_info(get_type_name(), "========================================", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Write Requests:    %0d", write_count), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Read Requests:     %0d", read_count), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Read Matches:      %0d", match_count), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Read Mismatches:   %0d", mismatch_count), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Pending Responses: %0d", expected_queue.size()), UVM_LOW)
        
        if (mismatch_count > 0 || expected_queue.size() > 0) begin
            `uvm_error(get_type_name(), "TEST FAILED!")
        end else begin
            `uvm_info(get_type_name(), "TEST PASSED!", UVM_LOW)
        end
        
        `uvm_info(get_type_name(), "========================================\n", UVM_LOW)
    endfunction
endclass

// Define analysis imp types
`uvm_analysis_imp_decl(_request)
`uvm_analysis_imp_decl(_response)

// ============================================================================
// Non-UVM Predictor Scoreboard
// ============================================================================
class simple_predictor_scoreboard;
    memory_predictor predictor;
    pred_transaction expected_queue[$];
    
    int match_count;
    int mismatch_count;
    
    function new();
        predictor = new();
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    function void add_request(pred_transaction tr);
        pred_transaction exp_tr = new();
        
        // Copy transaction
        exp_tr.addr = tr.addr;
        exp_tr.wdata = tr.wdata;
        exp_tr.write = tr.write;
        exp_tr.byte_en = tr.byte_en;
        
        // Predict
        predictor.predict(exp_tr);
        
        if (!exp_tr.write) begin
            // Store for read
            expected_queue.push_back(exp_tr);
            $display("[PRED_SB] Predicted read: addr=0x%08h data=0x%08h", 
                    exp_tr.addr, exp_tr.rdata);
        end
    endfunction
    
    function void add_response(pred_transaction tr);
        pred_transaction exp_tr;
        
        if (tr.write) return;  // Don't check writes
        
        if (expected_queue.size() == 0) begin
            $error("[PRED_SB] No expected response!");
            mismatch_count++;
            return;
        end
        
        exp_tr = expected_queue.pop_front();
        
        if (exp_tr.rdata == tr.rdata) begin
            $display("[PRED_SB] PASS: addr=0x%08h data=0x%08h", 
                    tr.addr, tr.rdata);
            match_count++;
        end else begin
            $error("[PRED_SB] FAIL: addr=0x%08h exp=0x%08h act=0x%08h", 
                  tr.addr, exp_tr.rdata, tr.rdata);
            mismatch_count++;
        end
    endfunction
    
    function void report();
        $display("\n=== Predictor Scoreboard Report ===");
        $display("Matches:    %0d", match_count);
        $display("Mismatches: %0d", mismatch_count);
        $display("Pending:    %0d", expected_queue.size());
        
        if (mismatch_count == 0 && expected_queue.size() == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
    endfunction
endclass

// ============================================================================
// Testbench (Non-UVM)
// ============================================================================
module predictor_scoreboard_tb;
    
    initial begin
        simple_predictor_scoreboard scb;
        pred_transaction tr;
        
        $display("\n=== Predictor Scoreboard Example ===\n");
        
        scb = new();
        
        // Test sequence: Write then Read
        $display("--- Test: Write then Read ---");
        
        // Write request
        tr = new();
        tr.addr = 32'h00001000;
        tr.wdata = 32'hDEADBEEF;
        tr.write = 1;
        tr.byte_en = 4'hF;
        scb.add_request(tr);
        
        // Write response (no checking needed)
        scb.add_response(tr);
        
        // Read request
        tr = new();
        tr.addr = 32'h00001000;
        tr.write = 0;
        tr.byte_en = 4'hF;
        scb.add_request(tr);
        
        // Read response (should match predicted)
        tr.rdata = 32'hDEADBEEF;  // Matches what was written
        scb.add_response(tr);
        
        // Another write
        tr = new();
        tr.addr = 32'h00002000;
        tr.wdata = 32'hCAFEBABE;
        tr.write = 1;
        tr.byte_en = 4'hF;
        scb.add_request(tr);
        scb.add_response(tr);
        
        // Read it back
        tr = new();
        tr.addr = 32'h00002000;
        tr.write = 0;
        tr.byte_en = 4'hF;
        scb.add_request(tr);
        tr.rdata = 32'hCAFEBABE;
        scb.add_response(tr);
        
        // Test partial write
        $display("\n--- Test: Partial Write (byte enables) ---");
        
        // Write only lower 2 bytes
        tr = new();
        tr.addr = 32'h00001000;
        tr.wdata = 32'h12345678;
        tr.write = 1;
        tr.byte_en = 4'b0011;  // Only bytes 0-1
        scb.add_request(tr);
        scb.add_response(tr);
        
        // Read back (should have upper bytes from before)
        tr = new();
        tr.addr = 32'h00001000;
        tr.write = 0;
        tr.byte_en = 4'hF;
        scb.add_request(tr);
        tr.rdata = 32'hDEAD5678;  // Upper bytes preserved
        scb.add_response(tr);
        
        // Final report
        scb.report();
        
        $display("\n=== Test Complete ===\n");
        $finish;
    end
    
endmodule

/*
 * PREDICTOR SCOREBOARD:
 * 
 * CONCEPT:
 * - Combines reference model + scoreboard
 * - Predictor generates expected outputs
 * - Scoreboard compares actual vs expected
 * - Most common scoreboard architecture
 * 
 * FLOW:
 * 1. Request → Predictor → Expected Output
 * 2. Expected Output → Queue
 * 3. DUT → Actual Output
 * 4. Compare: Expected vs Actual
 * 5. Report: Match/Mismatch
 * 
 * COMPONENTS:
 * 1. Predictor (Reference Model)
 *    - Behavioral model
 *    - Generates expected
 *    - High-level
 * 
 * 2. Scoreboard
 *    - Receives expected
 *    - Receives actual
 *    - Compares
 *    - Reports
 * 
 * ADVANTAGES:
 * + Automatic expected generation
 * + No manual expected values
 * + Scales well
 * + Reusable predictor
 * + Independent verification
 * 
 * DISADVANTAGES:
 * - Need accurate predictor
 * - Predictor can have bugs
 * - May miss RTL-specific issues
 * - More complex than simple scoreboard
 * 
 * USE CASES:
 * - Memory systems
 * - ALUs
 * - Data paths
 * - Protocol processing
 * - Any deterministic DUT
 * 
 * REQUEST/RESPONSE PATTERN:
 * 
 * For Writes:
 * 1. Request → Update predictor state
 * 2. Response → (optional check ack)
 * 
 * For Reads:
 * 1. Request → Query predictor for expected
 * 2. Expected → Queue
 * 3. Response → Compare with expected
 * 
 * IMPLEMENTATION STYLES:
 * 
 * 1. Inline Predictor:
 *    - Predictor logic in scoreboard
 *    - Simple, not reusable
 * 
 * 2. Separate Predictor:
 *    - Standalone predictor class
 *    - Reusable, testable
 *    - Recommended
 * 
 * 3. External Predictor (DPI-C):
 *    - C/C++/Python model
 *    - Software reuse
 *    - Performance
 * 
 * TIMING CONSIDERATIONS:
 * 
 * In-Order:
 * - FIFO queue for expected
 * - Match in order received
 * - Simple
 * 
 * Out-of-Order:
 * - Associative array for expected
 * - Match by ID/address
 * - More complex
 * 
 * UVM INTEGRATION:
 * - uvm_scoreboard base
 * - analysis_imp for request
 * - analysis_imp for response
 * - Automatic reporting
 * 
 * PREDICTION ACCURACY:
 * 
 * Exact:
 * - Bit-perfect match
 * - Strictest
 * - Best for simple logic
 * 
 * Approximate:
 * - Within tolerance
 * - For analog/DSP
 * - Floating-point
 * 
 * Masked:
 * - Ignore don't-care bits
 * - Partial comparison
 * - Flexible
 * 
 * BEST PRACTICES:
 * 1. Test predictor independently
 * 2. Separate predictor from scoreboard
 * 3. Handle all corner cases
 * 4. Clear error messages
 * 5. Track statistics
 * 6. Reset predictor state
 * 
 * ERROR HANDLING:
 * - Predictor errors (wrong logic)
 * - Missing responses
 * - Mismatches
 * - Order violations
 * 
 * STATE MANAGEMENT:
 * - Predictor maintains state
 * - Synchronize with DUT
 * - Reset handling
 * - State dump/restore
 * 
 * DEBUGGING:
 * - Log predictions
 * - Dump predictor state
 * - Compare step-by-step
 * - Isolate predictor vs DUT
 * 
 * VALIDATION:
 * ✓ Test predictor alone
 * ✓ Known input/output
 * ✓ Compare against spec
 * ✓ Review with designers
 * ✓ Cross-check with software
 * 
 * COMMON PREDICTORS:
 * - Memory: Read/write tracking
 * - ALU: Arithmetic operations
 * - FIFO: Queue behavior
 * - Cache: Hit/miss prediction
 * - Protocol: State machines
 * 
 * WHEN TO USE:
 * ✓ Deterministic behavior
 * ✓ Can model in software
 * ✓ Complex expected values
 * ✓ Many test cases
 * ✓ Reuse across tests
 * 
 * WHEN NOT TO USE:
 * ✗ Simple pass-through
 * ✗ Non-deterministic
 * ✗ Timing-dependent
 * ✗ Analog behavior
 * 
 * ALTERNATIVES:
 * - Self-checking testbench
 * - Explicit expected values
 * - Golden vectors
 * - Formal verification
 * 
 * METRICS:
 * - Prediction accuracy
 * - Match rate
 * - Mismatch rate
 * - Coverage
 * - Performance
 */
