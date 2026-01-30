// ============================================================================
// fifo_scoreboard.sv - In-Order FIFO-Based Scoreboard
// ============================================================================
// This scoreboard expects transactions in the same order they were sent
// Uses a FIFO queue to match expected vs actual transactions
// ============================================================================

// ============================================================================
// Transaction Class
// ============================================================================
class transaction;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit [1:0] trans_type;  // 0=READ, 1=WRITE, 2=RMW
    time timestamp;
    int trans_id;
    static int next_id = 0;
    
    function new();
        trans_id = next_id++;
        timestamp = $time;
    endfunction
    
    function bit compare(transaction tr);
        return (this.addr == tr.addr && 
                this.data == tr.data && 
                this.trans_type == tr.trans_type);
    endfunction
    
    function string convert2string();
        string trans_name;
        case (trans_type)
            0: trans_name = "READ";
            1: trans_name = "WRITE";
            2: trans_name = "RMW";
            default: trans_name = "UNKNOWN";
        endcase
        return $sformatf("[%0t] TXN#%0d %s addr=0x%08h data=0x%08h",
                        timestamp, trans_id, trans_name, addr, data);
    endfunction
    
    function void display(string prefix = "");
        $display("%s %s", prefix, convert2string());
    endfunction
endclass

// ============================================================================
// Basic FIFO Scoreboard (In-Order)
// ============================================================================
class fifo_scoreboard;
    transaction expected_queue[$];
    transaction actual_queue[$];
    
    int match_count;
    int mismatch_count;
    int expected_count;
    int actual_count;
    
    string name;
    
    function new(string scoreboard_name = "SCOREBOARD");
        name = scoreboard_name;
        match_count = 0;
        mismatch_count = 0;
        expected_count = 0;
        actual_count = 0;
    endfunction
    
    // Add expected transaction
    function void add_expected(transaction tr);
        expected_queue.push_back(tr);
        expected_count++;
        $display("[%s] Added expected TXN#%0d (queue size=%0d)", 
                name, tr.trans_id, expected_queue.size());
    endfunction
    
    // Add actual transaction (triggers comparison)
    function void add_actual(transaction tr);
        actual_queue.push_back(tr);
        actual_count++;
        $display("[%s] Received actual TXN#%0d (queue size=%0d)", 
                name, tr.trans_id, actual_queue.size());
        check_transaction();
    endfunction
    
    // Check transaction (FIFO order)
    function void check_transaction();
        transaction exp_tr, act_tr;
        
        if (expected_queue.size() == 0) begin
            $error("[%s] No expected transaction to match!", name);
            mismatch_count++;
            return;
        end
        
        if (actual_queue.size() == 0) begin
            return;  // Wait for actual transaction
        end
        
        // Pop from both queues (FIFO order)
        exp_tr = expected_queue.pop_front();
        act_tr = actual_queue.pop_front();
        
        // Compare
        if (exp_tr.compare(act_tr)) begin
            $display("[%s] PASS: Transactions match", name);
            exp_tr.display("  Expected:");
            act_tr.display("  Actual:  ");
            match_count++;
        end else begin
            $error("[%s] FAIL: Transaction mismatch!", name);
            exp_tr.display("  Expected:");
            act_tr.display("  Actual:  ");
            mismatch_count++;
            compare_detailed(exp_tr, act_tr);
        end
    endfunction
    
    // Detailed field-by-field comparison
    function void compare_detailed(transaction exp, transaction act);
        if (exp.addr != act.addr) begin
            $display("  → Address mismatch: exp=0x%08h act=0x%08h", 
                    exp.addr, act.addr);
        end
        
        if (exp.data != act.data) begin
            $display("  → Data mismatch: exp=0x%08h act=0x%08h", 
                    exp.data, act.data);
        end
        
        if (exp.trans_type != act.trans_type) begin
            $display("  → Type mismatch: exp=%0d act=%0d", 
                    exp.trans_type, act.trans_type);
        end
    endfunction
    
    // Report final statistics
    function void report();
        $display("\n");
        $display("========================================");
        $display("  %s FINAL REPORT", name);
        $display("========================================");
        $display("Expected Transactions: %0d", expected_count);
        $display("Actual Transactions:   %0d", actual_count);
        $display("Matches:               %0d", match_count);
        $display("Mismatches:            %0d", mismatch_count);
        $display("Pending Expected:      %0d", expected_queue.size());
        $display("Pending Actual:        %0d", actual_queue.size());
        
        if (expected_queue.size() > 0) begin
            $display("\nUnmatched Expected Transactions:");
            foreach(expected_queue[i]) begin
                expected_queue[i].display($sformatf("  [%0d]", i));
            end
        end
        
        if (actual_queue.size() > 0) begin
            $display("\nUnmatched Actual Transactions:");
            foreach(actual_queue[i]) begin
                actual_queue[i].display($sformatf("  [%0d]", i));
            end
        end
        
        $display("========================================");
        
        if (mismatch_count == 0 && 
            expected_queue.size() == 0 && 
            actual_queue.size() == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
        
        $display("========================================\n");
    endfunction
    
    // Dump queue contents
    function void dump_queues();
        $display("\n[%s] Queue Status:", name);
        $display("Expected Queue (size=%0d):", expected_queue.size());
        foreach(expected_queue[i]) begin
            expected_queue[i].display($sformatf("  [%0d]", i));
        end
        
        $display("Actual Queue (size=%0d):", actual_queue.size());
        foreach(actual_queue[i]) begin
            actual_queue[i].display($sformatf("  [%0d]", i));
        end
    endfunction
    
    // Clear all queues
    function void reset();
        expected_queue.delete();
        actual_queue.delete();
        match_count = 0;
        mismatch_count = 0;
        expected_count = 0;
        actual_count = 0;
        $display("[%s] Reset complete", name);
    endfunction
endclass

// ============================================================================
// Pipelined Scoreboard (Allows N Outstanding)
// ============================================================================
class pipelined_scoreboard;
    transaction expected_queue[$];
    int max_outstanding;
    int match_count;
    int mismatch_count;
    
    function new(int max_out = 16);
        max_outstanding = max_out;
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    function void add_expected(transaction tr);
        if (expected_queue.size() >= max_outstanding) begin
            $warning("Expected queue full, waiting...");
            wait(expected_queue.size() < max_outstanding);
        end
        expected_queue.push_back(tr);
    endfunction
    
    function void add_actual(transaction tr);
        transaction exp_tr;
        
        if (expected_queue.size() == 0) begin
            $error("No expected transaction!");
            mismatch_count++;
            return;
        end
        
        // Check against oldest expected (still FIFO)
        exp_tr = expected_queue.pop_front();
        
        if (exp_tr.compare(tr)) begin
            $display("PASS: Pipelined transaction matched");
            match_count++;
        end else begin
            $error("FAIL: Pipelined transaction mismatch");
            mismatch_count++;
        end
    endfunction
endclass

// ============================================================================
// Split Transaction Scoreboard (Request/Response)
// ============================================================================
class split_transaction_scoreboard;
    transaction request_queue[$];
    transaction pending_requests[int];  // Indexed by transaction ID
    int match_count;
    int mismatch_count;
    
    function new();
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    // Add request
    function void add_request(transaction req);
        pending_requests[req.trans_id] = req;
        $display("[SPLIT_SB] Added request TXN#%0d (pending=%0d)", 
                req.trans_id, pending_requests.size());
    endfunction
    
    // Add response (matches with request)
    function void add_response(transaction rsp);
        if (!pending_requests.exists(rsp.trans_id)) begin
            $error("[SPLIT_SB] No matching request for TXN#%0d", rsp.trans_id);
            mismatch_count++;
            return;
        end
        
        transaction req = pending_requests[rsp.trans_id];
        
        // For split transactions, typically only check data on reads
        if (req.trans_type == 0) begin  // READ
            if (req.data == rsp.data) begin
                $display("[SPLIT_SB] PASS: Read data matched for TXN#%0d", 
                        rsp.trans_id);
                match_count++;
            end else begin
                $error("[SPLIT_SB] FAIL: Read data mismatch for TXN#%0d", 
                      rsp.trans_id);
                $display("  Expected: 0x%08h", req.data);
                $display("  Actual:   0x%08h", rsp.data);
                mismatch_count++;
            end
        end else begin
            $display("[SPLIT_SB] Response received for TXN#%0d", rsp.trans_id);
            match_count++;
        end
        
        // Remove from pending
        pending_requests.delete(rsp.trans_id);
    endfunction
    
    function void report();
        $display("\n=== Split Transaction Scoreboard Report ===");
        $display("Matches:         %0d", match_count);
        $display("Mismatches:      %0d", mismatch_count);
        $display("Pending Requests: %0d", pending_requests.size());
        
        if (pending_requests.size() > 0) begin
            $display("\nPending Request IDs:");
            foreach(pending_requests[id]) begin
                $display("  TXN#%0d", id);
            end
        end
    endfunction
endclass

// ============================================================================
// Testbench
// ============================================================================
module fifo_scoreboard_tb;
    
    initial begin
        fifo_scoreboard scb;
        pipelined_scoreboard pipe_scb;
        split_transaction_scoreboard split_scb;
        transaction tr;
        
        $display("\n=== FIFO Scoreboard Examples ===\n");
        
        // Test 1: Basic FIFO scoreboard
        $display("--- Test 1: Basic FIFO Scoreboard ---");
        scb = new("FIFO_SB");
        
        // Perfect match scenario
        repeat(5) begin
            tr = new();
            assert(tr.randomize());
            scb.add_expected(tr);
            #10;
            scb.add_actual(tr);  // Same transaction
        end
        
        scb.report();
        
        // Test 2: Mismatch scenario
        $display("\n--- Test 2: Mismatch Scenario ---");
        scb = new("MISMATCH_SB");
        
        tr = new();
        assert(tr.randomize());
        scb.add_expected(tr);
        
        // Create different transaction
        tr = new();
        assert(tr.randomize());
        tr.addr = 32'hDEADBEEF;  // Force mismatch
        scb.add_actual(tr);
        
        scb.report();
        
        // Test 3: Order violation
        $display("\n--- Test 3: Order Matters ---");
        scb = new("ORDER_SB");
        
        // Add 3 expected in order
        for (int i = 0; i < 3; i++) begin
            tr = new();
            tr.addr = 32'h1000 + (i * 4);
            tr.data = 32'hA0 + i;
            tr.trans_type = 1;
            scb.add_expected(tr);
        end
        
        // Receive in different order - will fail!
        tr = new();
        tr.addr = 32'h1004;  // Should be 32'h1000
        tr.data = 32'hA1;
        tr.trans_type = 1;
        scb.add_actual(tr);
        
        scb.report();
        
        // Test 4: Pipelined scoreboard
        $display("\n--- Test 4: Pipelined Scoreboard ---");
        pipe_scb = new(4);
        
        // Add multiple outstanding
        for (int i = 0; i < 4; i++) begin
            tr = new();
            assert(tr.randomize());
            pipe_scb.add_expected(tr);
        end
        
        // Responses come back in order
        for (int i = 0; i < 4; i++) begin
            tr = new();
            assert(tr.randomize());
            pipe_scb.add_actual(tr);
        end
        
        $display("Pipelined: Matches=%0d, Mismatches=%0d", 
                pipe_scb.match_count, pipe_scb.mismatch_count);
        
        // Test 5: Split transaction
        $display("\n--- Test 5: Split Transaction Scoreboard ---");
        split_scb = new();
        
        // Send requests
        for (int i = 0; i < 3; i++) begin
            tr = new();
            tr.addr = 32'h2000 + (i * 4);
            tr.data = 32'hB0 + i;
            tr.trans_type = 0;  // READ
            split_scb.add_request(tr);
        end
        
        // Responses come back (same order for simplicity)
        for (int i = 0; i < 3; i++) begin
            tr = new();
            tr.trans_id = i;  // Match by ID
            tr.data = 32'hB0 + i;  // Matching data
            split_scb.add_response(tr);
        end
        
        split_scb.report();
        
        $display("\n=== All Tests Complete ===\n");
        $finish;
    end
    
endmodule

/*
 * FIFO SCOREBOARD:
 * 
 * CONCEPT:
 * - Expects transactions in the same order they were sent
 * - Uses FIFO queue for matching
 * - Simple and deterministic
 * - Good for in-order protocols
 * 
 * STRUCTURE:
 * 1. Expected Queue: Holds expected transactions
 * 2. Actual Queue: Holds received transactions
 * 3. Comparison: Match head of both queues
 * 
 * OPERATION:
 * add_expected(tr) → push to expected_queue
 * add_actual(tr)   → push to actual_queue, then compare
 * compare()        → pop_front from both, check match
 * 
 * ADVANTAGES:
 * + Simple implementation
 * + Deterministic matching
 * + Easy to debug
 * + Low memory usage
 * 
 * DISADVANTAGES:
 * - Requires strict ordering
 * - First mismatch blocks rest
 * - Can't handle out-of-order
 * - Not suitable for reordering protocols
 * 
 * USE CASES:
 * - FIFO designs
 * - In-order pipelines
 * - Simple protocols
 * - Point-to-point links
 * - Streaming interfaces
 * 
 * VARIATIONS:
 * 
 * 1. Immediate Comparison:
 *    - Compare as soon as actual arrives
 *    - Don't queue actual transactions
 *    - Lower latency
 * 
 * 2. Pipelined:
 *    - Allow N outstanding transactions
 *    - Still maintain order
 *    - Better for pipelined systems
 * 
 * 3. Split Transaction:
 *    - Separate request/response
 *    - Match by transaction ID
 *    - Handle latency
 * 
 * COMPARISON STRATEGIES:
 * 
 * 1. Exact Match:
 *    - All fields must match
 *    - Strictest checking
 * 
 * 2. Masked Match:
 *    - Ignore don't-care fields
 *    - Flexible checking
 * 
 * 3. Field-Specific:
 *    - Different rules per field
 *    - Custom comparison
 * 
 * ERROR HANDLING:
 * 
 * 1. No Expected:
 *    - Actual but no expected
 *    - Unexpected transaction
 * 
 * 2. No Actual:
 *    - Expected but no actual
 *    - Missing transaction
 * 
 * 3. Mismatch:
 *    - Both present but different
 *    - Data corruption
 * 
 * 4. Order Violation:
 *    - Wrong transaction order
 *    - Protocol error
 * 
 * BEST PRACTICES:
 * 1. Add timestamps
 * 2. Track transaction IDs
 * 3. Detailed error messages
 * 4. Dump queues on error
 * 5. Final statistics
 * 6. Timeout detection
 * 
 * DEBUGGING:
 * - dump_queues(): See what's pending
 * - Detailed comparison on mismatch
 * - Transaction IDs for tracking
 * - Timestamps for timing issues
 * 
 * WHEN NOT TO USE:
 * ✗ Out-of-order protocols (AXI, PCIe)
 * ✗ Multiple masters/slaves
 * ✗ Reordering allowed
 * ✗ Split transactions
 * 
 * ALTERNATIVES:
 * - Associative array scoreboard (out-of-order)
 * - Content-addressable scoreboard
 * - Reference model scoreboard
 * 
 * METRICS:
 * - Match count
 * - Mismatch count
 * - Pending expected
 * - Pending actual
 * - Pass rate
 * 
 * TYPICAL FLOW:
 * 1. Add expected transaction
 * 2. Wait for actual transaction
 * 3. Compare when actual arrives
 * 4. Report match/mismatch
 * 5. Repeat
 * 
 * ENHANCEMENTS:
 * - Add coverage tracking
 * - Performance metrics
 * - Latency measurement
 * - Bandwidth calculation
 * - Error injection testing
 */
