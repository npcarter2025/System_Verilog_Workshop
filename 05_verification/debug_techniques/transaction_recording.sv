// ============================================================================
// transaction_recording.sv - Transaction-Level Recording for Debug
// ============================================================================

// ============================================================================
// Transaction Class with Recording
// ============================================================================
class recorded_transaction;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit write;
    time timestamp;
    int transaction_id;
    static int next_id = 0;
    
    // Transaction recording file handle
    static int recording_file = 0;
    
    function new();
        transaction_id = next_id++;
        timestamp = $time;
    endfunction
    
    // Open recording file
    static function void open_recording(string filename = "transactions.log");
        recording_file = $fopen(filename, "w");
        if (recording_file) begin
            $fdisplay(recording_file, "# Transaction Recording Log");
            $fdisplay(recording_file, "# Format: ID, Time, Type, Address, Data");
            $fdisplay(recording_file, "#" );
            $display("[RECORD] Opened %s for transaction recording", filename);
        end else begin
            $error("[RECORD] Failed to open %s", filename);
        end
    endfunction
    
    // Close recording file
    static function void close_recording();
        if (recording_file) begin
            $fclose(recording_file);
            $display("[RECORD] Closed transaction recording file");
        end
    endfunction
    
    // Record this transaction
    function void record();
        if (recording_file) begin
            $fdisplay(recording_file, "%0d,%0t,%s,0x%08h,0x%08h",
                     transaction_id,
                     timestamp,
                     write ? "WRITE" : "READ",
                     addr,
                     data);
        end
    endfunction
    
    // Display transaction
    function void display(string prefix = "");
        $display("%s [%0t] TXN#%0d: %s addr=0x%08h data=0x%08h",
                prefix, timestamp, transaction_id,
                write ? "WRITE" : "READ", addr, data);
    endfunction
    
    // Convert to string
    function string convert2string();
        return $sformatf("[%0t] TXN#%0d: %s addr=0x%08h data=0x%08h",
                        timestamp, transaction_id,
                        write ? "WRITE" : "READ", addr, data);
    endfunction
endclass

// ============================================================================
// Transaction Queue with Recording
// ============================================================================
class transaction_queue;
    recorded_transaction queue[$];
    string queue_name;
    int max_size;
    
    function new(string name = "TXN_QUEUE", int max_sz = 1000);
        queue_name = name;
        max_size = max_sz;
    endfunction
    
    function void push(recorded_transaction tr);
        tr.record();  // Record when pushed
        queue.push_back(tr);
        
        // Limit queue size
        if (queue.size() > max_size) begin
            void'(queue.pop_front());
        end
        
        $display("[%s] Pushed TXN#%0d (size=%0d)", 
                queue_name, tr.transaction_id, queue.size());
    endfunction
    
    function recorded_transaction pop();
        if (queue.size() > 0) begin
            recorded_transaction tr = queue.pop_front();
            $display("[%s] Popped TXN#%0d (size=%0d)", 
                    queue_name, tr.transaction_id, queue.size());
            return tr;
        end else begin
            $warning("[%s] Attempted to pop from empty queue", queue_name);
            return null;
        end
    endfunction
    
    function void dump();
        $display("\n=== %s Contents (size=%0d) ===", queue_name, queue.size());
        foreach(queue[i]) begin
            $display("  [%0d] %s", i, queue[i].convert2string());
        end
    endfunction
    
    function void save_to_file(string filename);
        int fd = $fopen(filename, "w");
        if (fd) begin
            $fdisplay(fd, "# %s Snapshot at time %0t", queue_name, $time);
            foreach(queue[i]) begin
                $fdisplay(fd, "%s", queue[i].convert2string());
            end
            $fclose(fd);
            $display("[%s] Saved %0d transactions to %s", 
                    queue_name, queue.size(), filename);
        end
    endfunction
endclass

// ============================================================================
// Scoreboard with Transaction Recording
// ============================================================================
class recording_scoreboard;
    transaction_queue expected_queue;
    transaction_queue actual_queue;
    int match_count;
    int mismatch_count;
    int recording_fd;
    
    function new();
        expected_queue = new("EXPECTED");
        actual_queue = new("ACTUAL");
        match_count = 0;
        mismatch_count = 0;
        
        // Open results file
        recording_fd = $fopen("scoreboard_results.log", "w");
        $fdisplay(recording_fd, "# Scoreboard Results");
        $fdisplay(recording_fd, "# Time, Status, Expected, Actual");
    endfunction
    
    function void add_expected(recorded_transaction tr);
        expected_queue.push(tr);
    endfunction
    
    function void add_actual(recorded_transaction tr);
        actual_queue.push(tr);
        check_transaction(tr);
    endfunction
    
    function void check_transaction(recorded_transaction actual);
        recorded_transaction expected;
        
        if (expected_queue.queue.size() == 0) begin
            $error("[SCOREBOARD] No expected transaction for TXN#%0d", 
                  actual.transaction_id);
            mismatch_count++;
            record_result("UNEXPECTED", null, actual);
            return;
        end
        
        expected = expected_queue.pop();
        
        if (expected.addr == actual.addr && 
            expected.data == actual.data &&
            expected.write == actual.write) begin
            $display("[SCOREBOARD] PASS: TXN#%0d matches", actual.transaction_id);
            match_count++;
            record_result("PASS", expected, actual);
        end else begin
            $error("[SCOREBOARD] FAIL: TXN#%0d mismatch", actual.transaction_id);
            $display("  Expected: %s", expected.convert2string());
            $display("  Actual:   %s", actual.convert2string());
            mismatch_count++;
            record_result("FAIL", expected, actual);
        end
    endfunction
    
    function void record_result(string status, 
                                recorded_transaction exp, 
                                recorded_transaction act);
        $fdisplay(recording_fd, "%0t,%s,%s,%s",
                 $time,
                 status,
                 exp ? exp.convert2string() : "NONE",
                 act ? act.convert2string() : "NONE");
    endfunction
    
    function void report();
        $display("\n=== SCOREBOARD REPORT ===");
        $display("Matches:    %0d", match_count);
        $display("Mismatches: %0d", mismatch_count);
        $display("Pending Expected: %0d", expected_queue.queue.size());
        $display("Pending Actual:   %0d", actual_queue.queue.size());
        
        if (mismatch_count == 0 && expected_queue.queue.size() == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
        
        // Write final summary to file
        $fdisplay(recording_fd, "\n# Final Summary");
        $fdisplay(recording_fd, "# Matches: %0d", match_count);
        $fdisplay(recording_fd, "# Mismatches: %0d", mismatch_count);
        
        $fclose(recording_fd);
    endfunction
endclass

// ============================================================================
// CSV Transaction Logger
// ============================================================================
class csv_logger;
    int file_handle;
    string filename;
    
    function new(string fname = "transactions.csv");
        filename = fname;
        file_handle = $fopen(filename, "w");
        if (file_handle) begin
            // Write CSV header
            $fdisplay(file_handle, 
                     "Time,Transaction_ID,Type,Address,Data,Status");
            $display("[CSV_LOGGER] Opened %s", filename);
        end
    endfunction
    
    function void log_transaction(recorded_transaction tr, string status = "OK");
        if (file_handle) begin
            $fdisplay(file_handle, "%0t,%0d,%s,0x%08h,0x%08h,%s",
                     tr.timestamp,
                     tr.transaction_id,
                     tr.write ? "WRITE" : "READ",
                     tr.addr,
                     tr.data,
                     status);
        end
    endfunction
    
    function void close();
        if (file_handle) begin
            $fclose(file_handle);
            $display("[CSV_LOGGER] Closed %s", filename);
        end
    endfunction
endclass

// ============================================================================
// JSON Transaction Logger
// ============================================================================
class json_logger;
    int file_handle;
    string filename;
    bit first_entry;
    
    function new(string fname = "transactions.json");
        filename = fname;
        file_handle = $fopen(filename, "w");
        first_entry = 1;
        if (file_handle) begin
            $fdisplay(file_handle, "{");
            $fdisplay(file_handle, "  \"transactions\": [");
            $display("[JSON_LOGGER] Opened %s", filename);
        end
    endfunction
    
    function void log_transaction(recorded_transaction tr);
        if (file_handle) begin
            if (!first_entry) begin
                $fdisplay(file_handle, ",");
            end
            first_entry = 0;
            
            $fdisplay(file_handle, "    {");
            $fdisplay(file_handle, "      \"id\": %0d,", tr.transaction_id);
            $fdisplay(file_handle, "      \"time\": %0t,", tr.timestamp);
            $fdisplay(file_handle, "      \"type\": \"%s\",", 
                     tr.write ? "WRITE" : "READ");
            $fdisplay(file_handle, "      \"address\": \"0x%08h\",", tr.addr);
            $fdisplay(file_handle, "      \"data\": \"0x%08h\"", tr.data);
            $fwrite(file_handle, "    }");
        end
    endfunction
    
    function void close();
        if (file_handle) begin
            $fdisplay(file_handle, "");
            $fdisplay(file_handle, "  ]");
            $fdisplay(file_handle, "}");
            $fclose(file_handle);
            $display("[JSON_LOGGER] Closed %s", filename);
        end
    endfunction
endclass

// ============================================================================
// Performance Profiler
// ============================================================================
class transaction_profiler;
    real total_time;
    int transaction_count;
    real min_time, max_time, avg_time;
    time last_time;
    int profile_fd;
    
    function new(string filename = "profile.log");
        total_time = 0.0;
        transaction_count = 0;
        min_time = 1e9;
        max_time = 0.0;
        last_time = 0;
        
        profile_fd = $fopen(filename, "w");
        $fdisplay(profile_fd, "# Transaction Performance Profile");
    endfunction
    
    function void record_transaction(recorded_transaction tr);
        real delta;
        
        if (last_time > 0) begin
            delta = real'($time - last_time);
            total_time += delta;
            transaction_count++;
            
            if (delta < min_time) min_time = delta;
            if (delta > max_time) max_time = delta;
            avg_time = total_time / real'(transaction_count);
            
            $fdisplay(profile_fd, "%0t,%0d,%.2f,%.2f,%.2f,%.2f",
                     $time, tr.transaction_id, delta, 
                     min_time, max_time, avg_time);
        end
        
        last_time = $time;
    endfunction
    
    function void report();
        $display("\n=== PERFORMANCE PROFILE ===");
        $display("Total Transactions: %0d", transaction_count);
        $display("Min Time: %.2f ns", min_time);
        $display("Max Time: %.2f ns", max_time);
        $display("Avg Time: %.2f ns", avg_time);
        $display("Total Time: %.2f ns", total_time);
        
        if (transaction_count > 0) begin
            $display("Throughput: %.2f transactions/us", 
                    real'(transaction_count) * 1000.0 / total_time);
        end
        
        $fclose(profile_fd);
    endfunction
endclass

// ============================================================================
// Test Module
// ============================================================================
module transaction_recording;
    logic clk, rst_n;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset
    initial begin
        rst_n = 0;
        #50 rst_n = 1;
    end
    
    // Test
    initial begin
        recorded_transaction tr;
        recording_scoreboard scb;
        csv_logger csv;
        json_logger json;
        transaction_profiler profiler;
        
        @(posedge rst_n);
        @(posedge clk);
        
        $display("\n=== Transaction Recording Examples ===\n");
        
        // Open recording
        recorded_transaction::open_recording("transactions.log");
        
        // Create components
        scb = new();
        csv = new("transactions.csv");
        json = new("transactions.json");
        profiler = new("performance.log");
        
        // Generate and record transactions
        repeat(10) begin
            @(posedge clk);
            
            // Create transaction
            tr = new();
            assert(tr.randomize());
            
            // Record in various formats
            tr.record();
            tr.display("[TEST]");
            csv.log_transaction(tr, "OK");
            json.log_transaction(tr);
            profiler.record_transaction(tr);
            
            // Add to scoreboard
            scb.add_expected(tr);
            scb.add_actual(tr);  // Simulate perfect match
        end
        
        // Final reports
        #100;
        scb.report();
        profiler.report();
        
        // Close files
        recorded_transaction::close_recording();
        csv.close();
        json.close();
        
        $display("\n=== Test Complete ===\n");
        #100;
        $finish;
    end
    
endmodule

/*
 * TRANSACTION RECORDING:
 * 
 * WHY RECORD TRANSACTIONS?
 * 1. Post-mortem debug (what happened?)
 * 2. Regression comparison
 * 3. Performance analysis
 * 4. Coverage analysis
 * 5. Test reproducibility
 * 6. Communication with others
 * 
 * WHAT TO RECORD:
 * - Transaction fields
 * - Timestamps
 * - Transaction ID
 * - Status (pass/fail)
 * - Relationships (request/response)
 * - Performance metrics
 * 
 * RECORDING FORMATS:
 * 
 * 1. Plain Text Log:
 *    + Easy to read
 *    + grep/awk/sed friendly
 *    - Unstructured
 *    - Hard to parse programmatically
 * 
 * 2. CSV (Comma-Separated):
 *    + Easy to parse
 *    + Excel/spreadsheet compatible
 *    + Good for analysis
 *    - Less human-readable
 * 
 * 3. JSON:
 *    + Structured
 *    + Language-agnostic
 *    + Easy to parse
 *    + Supports nesting
 *    - Larger files
 * 
 * 4. Binary:
 *    + Compact
 *    + Fast
 *    - Not human-readable
 *    - Tool-dependent
 * 
 * WHEN TO RECORD:
 * - Always: Basic transaction log
 * - Debug: Detailed fields
 * - Performance: Timing info
 * - Regression: Comparison data
 * 
 * FILE MANAGEMENT:
 * 
 * Opening:
 * fd = $fopen("file.log", "w");  // Write
 * fd = $fopen("file.log", "a");  // Append
 * 
 * Writing:
 * $fdisplay(fd, "format", args);
 * $fwrite(fd, "format", args);
 * 
 * Closing:
 * $fclose(fd);
 * 
 * BEST PRACTICES:
 * 
 * 1. Unique Transaction IDs
 *    - Auto-increment
 *    - Never reuse
 *    - Track relationships
 * 
 * 2. Timestamps
 *    - Record $time
 *    - Useful for timing analysis
 *    - Debug race conditions
 * 
 * 3. Structured Output
 *    - Consistent format
 *    - Easy parsing
 *    - Header with field names
 * 
 * 4. Selective Recording
 *    - Don't log everything
 *    - Filter by type/address
 *    - Control via plusargs
 * 
 * 5. File Size Control
 *    - Rotate logs
 *    - Compress old files
 *    - Limit depth
 * 
 * 6. Performance Impact
 *    - File I/O is slow
 *    - Buffer writes
 *    - Consider binary format
 * 
 * ANALYSIS TOOLS:
 * - grep, awk, sed (text)
 * - Python pandas (CSV)
 * - jq (JSON)
 * - Custom scripts
 * 
 * DEBUGGING WITH RECORDINGS:
 * 
 * 1. Find failing transaction:
 *    grep "FAIL" scoreboard.log
 * 
 * 2. Extract specific type:
 *    grep "WRITE" transactions.log
 * 
 * 3. Time window:
 *    awk '$1 > 1000 && $1 < 2000' trans.csv
 * 
 * 4. Count operations:
 *    grep -c "READ" transactions.log
 * 
 * COMMON PATTERNS:
 * 
 * 1. Before/After Comparison:
 *    - Record expected
 *    - Record actual
 *    - Compare files
 * 
 * 2. Golden Reference:
 *    - Save known-good log
 *    - Compare new runs
 *    - Detect regressions
 * 
 * 3. Performance Tracking:
 *    - Record timestamps
 *    - Calculate deltas
 *    - Identify bottlenecks
 * 
 * 4. Coverage Holes:
 *    - Record all transactions
 *    - Analyze patterns
 *    - Find missing cases
 * 
 * INTEGRATION WITH UVM:
 * - uvm_recorder
 * - uvm_tr_database
 * - Automatic recording
 * - Tool integration
 * 
 * TIPS:
 * - Use transaction IDs
 * - Include timestamps
 * - Format consistently
 * - Comment file format
 * - Automate analysis
 * - Version control test vectors
 */
