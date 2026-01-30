// ============================================================================
// associative_array_sb.sv - Out-of-Order Scoreboard Using Associative Arrays
// ============================================================================
// This scoreboard can handle transactions that complete out-of-order
// Uses associative arrays indexed by unique keys (address, ID, etc.)
// ============================================================================

// ============================================================================
// Transaction Class
// ============================================================================
class reorder_transaction;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit [7:0] trans_id;
    rand bit [1:0] trans_type;  // 0=READ, 1=WRITE
    time timestamp;
    
    constraint addr_c {
        addr[1:0] == 2'b00;  // Word aligned
    }
    
    function new();
        timestamp = $time;
    endfunction
    
    function bit compare(reorder_transaction tr);
        // Compare relevant fields
        if (trans_type == 0) begin  // READ: compare data
            return (this.data == tr.data);
        end else begin  // WRITE: just acknowledge
            return 1;
        end
    endfunction
    
    function string convert2string();
        string type_str = (trans_type == 0) ? "READ" : "WRITE";
        return $sformatf("[%0t] TXN#%0d %s addr=0x%08h data=0x%08h",
                        timestamp, trans_id, type_str, addr, data);
    endfunction
endclass

// ============================================================================
// Associative Array Scoreboard (Address-Based)
// ============================================================================
class associative_array_scoreboard;
    // Associative arrays indexed by address
    reorder_transaction expected_by_addr[bit [31:0]];
    reorder_transaction actual_by_addr[bit [31:0]];
    
    int match_count;
    int mismatch_count;
    int pending_expected;
    int pending_actual;
    
    string name;
    
    function new(string sb_name = "ASSOC_SB");
        name = sb_name;
        match_count = 0;
        mismatch_count = 0;
        pending_expected = 0;
        pending_actual = 0;
    endfunction
    
    // Add expected transaction
    function void add_expected(reorder_transaction tr);
        if (expected_by_addr.exists(tr.addr)) begin
            $warning("[%s] Overwriting expected transaction at addr 0x%08h", 
                    name, tr.addr);
        end
        
        expected_by_addr[tr.addr] = tr;
        pending_expected++;
        
        $display("[%s] Added expected: %s (pending=%0d)", 
                name, tr.convert2string(), pending_expected);
        
        // Try to match with any pending actual
        check_by_address(tr.addr);
    endfunction
    
    // Add actual transaction
    function void add_actual(reorder_transaction tr);
        $display("[%s] Received actual: %s", name, tr.convert2string());
        
        // Check if we have matching expected
        if (expected_by_addr.exists(tr.addr)) begin
            check_transaction(expected_by_addr[tr.addr], tr);
            expected_by_addr.delete(tr.addr);
            pending_expected--;
        end else begin
            // Store for later matching
            actual_by_addr[tr.addr] = tr;
            pending_actual++;
            $display("[%s] No expected yet, storing actual (pending=%0d)", 
                    name, pending_actual);
        end
    endfunction
    
    // Check if address can be matched
    function void check_by_address(bit [31:0] addr);
        if (actual_by_addr.exists(addr)) begin
            check_transaction(expected_by_addr[addr], actual_by_addr[addr]);
            actual_by_addr.delete(addr);
            expected_by_addr.delete(addr);
            pending_actual--;
            pending_expected--;
        end
    endfunction
    
    // Compare two transactions
    function void check_transaction(reorder_transaction exp, reorder_transaction act);
        if (exp.compare(act)) begin
            $display("[%s] PASS: Match at addr 0x%08h", name, exp.addr);
            $display("  Expected: %s", exp.convert2string());
            $display("  Actual:   %s", act.convert2string());
            match_count++;
        end else begin
            $error("[%s] FAIL: Mismatch at addr 0x%08h", name, exp.addr);
            $display("  Expected: %s", exp.convert2string());
            $display("  Actual:   %s", act.convert2string());
            mismatch_count++;
        end
    endfunction
    
    // Report
    function void report();
        $display("\n========================================");
        $display("  %s FINAL REPORT", name);
        $display("========================================");
        $display("Matches:           %0d", match_count);
        $display("Mismatches:        %0d", mismatch_count);
        $display("Pending Expected:  %0d", pending_expected);
        $display("Pending Actual:    %0d", pending_actual);
        
        if (pending_expected > 0) begin
            $display("\nUnmatched Expected Transactions:");
            foreach(expected_by_addr[addr]) begin
                $display("  Addr 0x%08h: %s", addr, 
                        expected_by_addr[addr].convert2string());
            end
        end
        
        if (pending_actual > 0) begin
            $display("\nUnmatched Actual Transactions:");
            foreach(actual_by_addr[addr]) begin
                $display("  Addr 0x%08h: %s", addr, 
                        actual_by_addr[addr].convert2string());
            end
        end
        
        $display("========================================");
        
        if (mismatch_count == 0 && pending_expected == 0 && pending_actual == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
        
        $display("========================================\n");
    endfunction
endclass

// ============================================================================
// ID-Based Scoreboard (For Tagged Transactions)
// ============================================================================
class id_based_scoreboard;
    reorder_transaction expected_by_id[bit [7:0]];
    reorder_transaction actual_by_id[bit [7:0]];
    
    int match_count;
    int mismatch_count;
    
    function new();
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    function void add_expected(reorder_transaction tr);
        expected_by_id[tr.trans_id] = tr;
        $display("[ID_SB] Added expected TXN#%0d", tr.trans_id);
        check_by_id(tr.trans_id);
    endfunction
    
    function void add_actual(reorder_transaction tr);
        $display("[ID_SB] Received actual TXN#%0d", tr.trans_id);
        
        if (expected_by_id.exists(tr.trans_id)) begin
            check_transaction(expected_by_id[tr.trans_id], tr);
            expected_by_id.delete(tr.trans_id);
        end else begin
            actual_by_id[tr.trans_id] = tr;
            $display("[ID_SB] Storing actual for later match");
        end
    endfunction
    
    function void check_by_id(bit [7:0] id);
        if (actual_by_id.exists(id)) begin
            check_transaction(expected_by_id[id], actual_by_id[id]);
            actual_by_id.delete(id);
            expected_by_id.delete(id);
        end
    endfunction
    
    function void check_transaction(reorder_transaction exp, reorder_transaction act);
        if (exp.compare(act)) begin
            $display("[ID_SB] PASS: TXN#%0d matched", exp.trans_id);
            match_count++;
        end else begin
            $error("[ID_SB] FAIL: TXN#%0d mismatch", exp.trans_id);
            mismatch_count++;
        end
    endfunction
    
    function void report();
        $display("\n=== ID-Based Scoreboard Report ===");
        $display("Matches:    %0d", match_count);
        $display("Mismatches: %0d", mismatch_count);
        $display("Pending Expected: %0d", expected_by_id.size());
        $display("Pending Actual:   %0d", actual_by_id.size());
    endfunction
endclass

// ============================================================================
// Multi-Key Scoreboard (Address + ID)
// ============================================================================
typedef struct {
    bit [31:0] addr;
    bit [7:0] id;
} composite_key_t;

class multi_key_scoreboard;
    reorder_transaction expected[composite_key_t];
    reorder_transaction actual[composite_key_t];
    
    int match_count;
    int mismatch_count;
    
    function new();
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    function composite_key_t make_key(reorder_transaction tr);
        composite_key_t key;
        key.addr = tr.addr;
        key.id = tr.trans_id;
        return key;
    endfunction
    
    function void add_expected(reorder_transaction tr);
        composite_key_t key = make_key(tr);
        expected[key] = tr;
        $display("[MULTI_SB] Added expected with key (addr=0x%08h, id=%0d)", 
                key.addr, key.id);
        check_by_key(key);
    endfunction
    
    function void add_actual(reorder_transaction tr);
        composite_key_t key = make_key(tr);
        $display("[MULTI_SB] Received actual with key (addr=0x%08h, id=%0d)", 
                key.addr, key.id);
        
        if (expected.exists(key)) begin
            check_transaction(expected[key], tr);
            expected.delete(key);
        end else begin
            actual[key] = tr;
        end
    endfunction
    
    function void check_by_key(composite_key_t key);
        if (actual.exists(key)) begin
            check_transaction(expected[key], actual[key]);
            actual.delete(key);
            expected.delete(key);
        end
    endfunction
    
    function void check_transaction(reorder_transaction exp, reorder_transaction act);
        if (exp.compare(act)) begin
            $display("[MULTI_SB] PASS: Transaction matched");
            match_count++;
        end else begin
            $error("[MULTI_SB] FAIL: Transaction mismatch");
            mismatch_count++;
        end
    endfunction
    
    function void report();
        $display("\n=== Multi-Key Scoreboard Report ===");
        $display("Matches:    %0d", match_count);
        $display("Mismatches: %0d", mismatch_count);
        $display("Pending:    %0d", expected.size() + actual.size());
    endfunction
endclass

// ============================================================================
// Content-Addressable Scoreboard (Find by Content)
// ============================================================================
class content_addressable_scoreboard;
    reorder_transaction expected_queue[$];
    reorder_transaction actual_queue[$];
    
    int match_count;
    int mismatch_count;
    
    function new();
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    function void add_expected(reorder_transaction tr);
        expected_queue.push_back(tr);
        $display("[CA_SB] Added expected (queue size=%0d)", expected_queue.size());
    endfunction
    
    function void add_actual(reorder_transaction tr);
        int found_idx = -1;
        
        $display("[CA_SB] Searching for match...");
        
        // Search through expected queue
        foreach(expected_queue[i]) begin
            if (expected_queue[i].addr == tr.addr && 
                expected_queue[i].trans_id == tr.trans_id) begin
                found_idx = i;
                break;
            end
        end
        
        if (found_idx >= 0) begin
            reorder_transaction exp = expected_queue[found_idx];
            
            if (exp.compare(tr)) begin
                $display("[CA_SB] PASS: Found match at index %0d", found_idx);
                match_count++;
            end else begin
                $error("[CA_SB] FAIL: Found but data mismatch");
                mismatch_count++;
            end
            
            // Remove from queue
            expected_queue.delete(found_idx);
        end else begin
            $display("[CA_SB] No match found, queuing actual");
            actual_queue.push_back(tr);
        end
    endfunction
    
    function void report();
        $display("\n=== Content-Addressable Scoreboard Report ===");
        $display("Matches:    %0d", match_count);
        $display("Mismatches: %0d", mismatch_count);
        $display("Pending Expected: %0d", expected_queue.size());
        $display("Pending Actual:   %0d", actual_queue.size());
    endfunction
endclass

// ============================================================================
// Testbench
// ============================================================================
module associative_array_sb_tb;
    
    initial begin
        associative_array_scoreboard addr_scb;
        id_based_scoreboard id_scb;
        multi_key_scoreboard multi_scb;
        content_addressable_scoreboard ca_scb;
        reorder_transaction tr;
        reorder_transaction transactions[$];
        
        $display("\n=== Out-of-Order Scoreboard Examples ===\n");
        
        // Test 1: Address-based (Out of Order)
        $display("--- Test 1: Address-Based Out-of-Order ---");
        addr_scb = new("ADDR_REORDER_SB");
        
        // Generate 5 expected transactions
        for (int i = 0; i < 5; i++) begin
            tr = new();
            tr.addr = 32'h1000 + (i * 4);
            tr.data = 32'hA0 + i;
            tr.trans_type = 0;  // READ
            tr.trans_id = i;
            addr_scb.add_expected(tr);
            transactions.push_back(tr);
        end
        
        // Receive in different order: 2, 0, 4, 1, 3
        int order[$] = {2, 0, 4, 1, 3};
        foreach(order[i]) begin
            #10;
            tr = transactions[order[i]];
            addr_scb.add_actual(tr);
        end
        
        addr_scb.report();
        
        // Test 2: ID-based
        $display("\n--- Test 2: ID-Based Scoreboard ---");
        id_scb = new();
        transactions.delete();
        
        // Generate expected
        for (int i = 0; i < 4; i++) begin
            tr = new();
            tr.trans_id = 8'd(i * 10);
            tr.addr = 32'h2000 + (i * 4);
            tr.data = 32'hB0 + i;
            id_scb.add_expected(tr);
            transactions.push_back(tr);
        end
        
        // Receive out of order by ID
        id_scb.add_actual(transactions[3]);  // ID 30
        #5;
        id_scb.add_actual(transactions[0]);  // ID 0
        #5;
        id_scb.add_actual(transactions[2]);  // ID 20
        #5;
        id_scb.add_actual(transactions[1]);  // ID 10
        
        id_scb.report();
        
        // Test 3: Multi-key
        $display("\n--- Test 3: Multi-Key (Addr + ID) Scoreboard ---");
        multi_scb = new();
        
        for (int i = 0; i < 3; i++) begin
            tr = new();
            tr.addr = 32'h3000 + (i * 4);
            tr.trans_id = i;
            tr.data = 32'hC0 + i;
            multi_scb.add_expected(tr);
        end
        
        // Out of order
        tr = new();
        tr.addr = 32'h3008;
        tr.trans_id = 2;
        tr.data = 32'hC2;
        multi_scb.add_actual(tr);
        
        tr = new();
        tr.addr = 32'h3000;
        tr.trans_id = 0;
        tr.data = 32'hC0;
        multi_scb.add_actual(tr);
        
        tr = new();
        tr.addr = 32'h3004;
        tr.trans_id = 1;
        tr.data = 32'hC1;
        multi_scb.add_actual(tr);
        
        multi_scb.report();
        
        // Test 4: Content-addressable
        $display("\n--- Test 4: Content-Addressable Scoreboard ---");
        ca_scb = new();
        
        for (int i = 0; i < 3; i++) begin
            tr = new();
            assert(tr.randomize());
            ca_scb.add_expected(tr);
        end
        
        // Will search through queue to find matches
        for (int i = 0; i < 3; i++) begin
            tr = new();
            assert(tr.randomize());
            ca_scb.add_actual(tr);
        end
        
        ca_scb.report();
        
        $display("\n=== All Tests Complete ===\n");
        $finish;
    end
    
endmodule

/*
 * OUT-OF-ORDER SCOREBOARD:
 * 
 * CONCEPT:
 * - Transactions can complete in any order
 * - Match by unique key (address, ID, etc.)
 * - Uses associative arrays for O(1) lookup
 * - Essential for reordering protocols
 * 
 * KEY TYPES:
 * 
 * 1. Address-Based:
 *    - Key: Transaction address
 *    - Good for: Memory systems, caches
 *    - Example: expected[addr] = transaction
 * 
 * 2. ID-Based:
 *    - Key: Transaction ID
 *    - Good for: Tagged protocols (AXI, PCIe)
 *    - Example: expected[id] = transaction
 * 
 * 3. Multi-Key:
 *    - Key: Composite (addr + id)
 *    - Good for: Complex protocols
 *    - Example: expected[{addr,id}] = transaction
 * 
 * 4. Content-Addressable:
 *    - Search by content
 *    - Most flexible
 *    - Slower (O(n) search)
 * 
 * ASSOCIATIVE ARRAY:
 * datatype array_name [key_type];
 * 
 * Methods:
 * - exists(key): Check if key exists
 * - delete(key): Remove entry
 * - first()/next(): Iterate
 * - size(): Number of entries
 * - num(): Same as size()
 * 
 * OPERATION:
 * 1. add_expected(tr):
 *    - Store in expected[key]
 *    - Check if matching actual exists
 * 
 * 2. add_actual(tr):
 *    - Look up expected[key]
 *    - If exists: compare and remove
 *    - If not: store in actual[key]
 * 
 * ADVANTAGES:
 * + Handles out-of-order
 * + O(1) lookup time
 * + Flexible key selection
 * + Natural for tagged protocols
 * 
 * DISADVANTAGES:
 * - More complex than FIFO
 * - Higher memory usage
 * - Need unique keys
 * - Debugging harder
 * 
 * USE CASES:
 * - AXI (ID-based reordering)
 * - PCIe (tag-based)
 * - NoC (packet routing)
 * - Caches (address-based)
 * - OOO processors
 * 
 * KEY SELECTION:
 * 
 * Good Keys:
 * ✓ Unique for each transaction
 * ✓ Available early
 * ✓ Small data type
 * ✓ Easy to extract
 * 
 * Bad Keys:
 * ✗ Non-unique
 * ✗ Changes during transaction
 * ✗ Large structures
 * ✗ Complex to compute
 * 
 * MATCHING STRATEGIES:
 * 
 * 1. Immediate Match:
 *    - Try to match as soon as received
 *    - Low latency
 * 
 * 2. Deferred Match:
 *    - Store and match later
 *    - More flexible
 * 
 * 3. Timeout-Based:
 *    - Match within time window
 *    - Detect hangs
 * 
 * COMPOSITE KEYS:
 * typedef struct {
 *     bit [31:0] addr;
 *     bit [7:0] id;
 * } key_t;
 * 
 * transaction array[key_t];
 * 
 * ITERATION:
 * bit [31:0] addr;
 * 
 * if (array.first(addr)) begin
 *     do begin
 *         // Process array[addr]
 *     end while(array.next(addr));
 * end
 * 
 * BEST PRACTICES:
 * 1. Choose appropriate key type
 * 2. Check exists() before access
 * 3. Delete after matching
 * 4. Handle missing matches
 * 5. Report unmatched at end
 * 6. Add timeouts
 * 
 * ERROR SCENARIOS:
 * 
 * 1. Duplicate Key:
 *    - New transaction with existing key
 *    - Overwrite or error?
 * 
 * 2. Missing Expected:
 *    - Actual arrives, no expected
 *    - Protocol violation
 * 
 * 3. Missing Actual:
 *    - Expected never matched
 *    - Lost transaction
 * 
 * 4. Mismatch:
 *    - Key matches but data doesn't
 *    - Data corruption
 * 
 * DEBUGGING:
 * - Print key on add
 * - Dump unmatched keys
 * - Track arrival order
 * - Timeout detection
 * - Key collision checking
 * 
 * PERFORMANCE:
 * - Associative array: O(1) lookup
 * - Queue search: O(n) lookup
 * - Memory: O(outstanding transactions)
 * - Choose based on protocol
 * 
 * COMPARISON:
 * 
 * FIFO Scoreboard:
 * + Simple
 * + In-order only
 * + O(1) match
 * 
 * Associative Scoreboard:
 * + Out-of-order
 * + More complex
 * + O(1) match
 * + Requires unique key
 * 
 * Content-Addressable:
 * + Most flexible
 * + No unique key needed
 * - O(n) search
 * 
 * WHEN TO USE:
 * ✓ Protocol allows reordering
 * ✓ Have unique identifier
 * ✓ Need high performance
 * ✓ Many outstanding transactions
 * 
 * TYPICAL PROTOCOLS:
 * - AXI: ID-based
 * - PCIe: Tag-based
 * - Network: Packet ID
 * - Cache: Address-based
 */
