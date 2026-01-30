// ============================================================================
// uvm_debug_messaging.sv - UVM Debug and Messaging Techniques
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// Transaction with Debug Messages
// ============================================================================
class debug_transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit write;
    
    `uvm_object_utils_begin(debug_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(write, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "debug_transaction");
        super.new(name);
    endfunction
    
    function void post_randomize();
        // Debug: Log after randomization
        `uvm_info(get_type_name(), 
                 $sformatf("Randomized: %s addr=0x%0h data=0x%0h", 
                          write ? "WRITE" : "READ", addr, data),
                 UVM_HIGH)
    endfunction
endclass

// ============================================================================
// Driver with Verbosity Control
// ============================================================================
class debug_driver extends uvm_driver #(debug_transaction);
    `uvm_component_utils(debug_driver)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        debug_transaction tr;
        
        forever begin
            seq_item_port.get_next_item(tr);
            
            // Different verbosity levels
            `uvm_info(get_type_name(), 
                     $sformatf("Got transaction: %s", tr.convert2string()),
                     UVM_MEDIUM)
            
            `uvm_info(get_type_name(), 
                     "Starting to drive transaction",
                     UVM_HIGH)
            
            drive_transaction(tr);
            
            `uvm_info(get_type_name(), 
                     "Transaction complete",
                     UVM_HIGH)
            
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(debug_transaction tr);
        // Detailed debug at UVM_DEBUG level
        `uvm_info(get_type_name(), 
                 $sformatf("Driving: addr=0x%0h", tr.addr),
                 UVM_DEBUG)
        
        #10;  // Simulate driving time
        
        `uvm_info(get_type_name(), 
                 $sformatf("Driven: data=0x%0h", tr.data),
                 UVM_DEBUG)
    endtask
endclass

// ============================================================================
// Monitor with Error Checking
// ============================================================================
class debug_monitor extends uvm_monitor;
    `uvm_component_utils(debug_monitor)
    
    uvm_analysis_port #(debug_transaction) ap;
    int transaction_count;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        debug_transaction tr;
        
        forever begin
            tr = debug_transaction::type_id::create("tr");
            
            // Simulate monitoring
            #20;
            assert(tr.randomize());
            
            transaction_count++;
            
            // Log with different severities
            if (tr.addr == 32'h0) begin
                `uvm_warning(get_type_name(), 
                           "Transaction to address 0 detected!")
            end
            
            if (tr.addr > 32'hFFFF) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Address out of range: 0x%0h", tr.addr))
            end
            
            `uvm_info(get_type_name(), 
                     $sformatf("Monitored TXN#%0d: %s", 
                              transaction_count, tr.convert2string()),
                     UVM_MEDIUM)
            
            ap.write(tr);
        end
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                 $sformatf("Monitored %0d transactions", transaction_count),
                 UVM_LOW)
    endfunction
endclass

// ============================================================================
// Scoreboard with Detailed Comparison
// ============================================================================
class debug_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(debug_scoreboard)
    
    uvm_analysis_imp #(debug_transaction, debug_scoreboard) analysis_export;
    debug_transaction expected_queue[$];
    int match_count;
    int mismatch_count;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction
    
    function void write(debug_transaction tr);
        debug_transaction exp;
        
        if (expected_queue.size() == 0) begin
            `uvm_error(get_type_name(), 
                      $sformatf("No expected transaction for: %s", 
                               tr.convert2string()))
            mismatch_count++;
            return;
        end
        
        exp = expected_queue.pop_front();
        
        if (compare(exp, tr)) begin
            `uvm_info(get_type_name(), 
                     $sformatf("PASS: Transaction matched"), 
                     UVM_HIGH)
            match_count++;
        end else begin
            `uvm_error(get_type_name(), 
                      "Transaction mismatch!")
            `uvm_info(get_type_name(), 
                     $sformatf("Expected: %s", exp.convert2string()),
                     UVM_NONE)
            `uvm_info(get_type_name(), 
                     $sformatf("Actual:   %s", tr.convert2string()),
                     UVM_NONE)
            mismatch_count++;
        end
    endfunction
    
    function bit compare(debug_transaction exp, debug_transaction act);
        bit result = 1;
        
        if (exp.addr != act.addr) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Address mismatch: exp=0x%0h act=0x%0h", 
                               exp.addr, act.addr))
            result = 0;
        end
        
        if (exp.data != act.data) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Data mismatch: exp=0x%0h act=0x%0h", 
                               exp.data, act.data))
            result = 0;
        end
        
        if (exp.write != act.write) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Write mismatch: exp=%0b act=%0b", 
                               exp.write, act.write))
            result = 0;
        end
        
        return result;
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                 $sformatf("\n=== SCOREBOARD REPORT ===\n" ),
                 UVM_LOW)
        `uvm_info(get_type_name(), 
                 $sformatf("Matches:    %0d", match_count),
                 UVM_LOW)
        `uvm_info(get_type_name(), 
                 $sformatf("Mismatches: %0d", mismatch_count),
                 UVM_LOW)
        
        if (mismatch_count > 0) begin
            `uvm_error(get_type_name(), "TEST FAILED!")
        end else begin
            `uvm_info(get_type_name(), "TEST PASSED!", UVM_LOW)
        end
    endfunction
endclass

// ============================================================================
// Test with Debug Control
// ============================================================================
class debug_test extends uvm_test;
    `uvm_component_utils(debug_test)
    
    debug_driver drv;
    debug_monitor mon;
    debug_scoreboard scb;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable/disable debug messages via command line
        // +UVM_VERBOSITY=UVM_HIGH
        // +UVM_VERBOSITY=UVM_DEBUG
        
        drv = debug_driver::type_id::create("drv", this);
        mon = debug_monitor::type_id::create("mon", this);
        scb = debug_scoreboard::type_id::create("scb", this);
        
        `uvm_info(get_type_name(), "Build phase complete", UVM_MEDIUM)
    endfunction
    
    function void connect_phase(uvm_phase phase);
        mon.ap.connect(scb.analysis_export);
        `uvm_info(get_type_name(), "Connect phase complete", UVM_MEDIUM)
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        // Print testbench topology
        `uvm_info(get_type_name(), "Testbench Topology:", UVM_LOW)
        this.print();
        
        // Print factory configuration
        `uvm_info(get_type_name(), "Factory Configuration:", UVM_MEDIUM)
        factory.print();
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Test starting", UVM_LOW)
        
        #1000;
        
        `uvm_info(get_type_name(), "Test complete", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        uvm_report_server rs;
        int error_count;
        
        rs = uvm_report_server::get_server();
        error_count = rs.get_severity_count(UVM_ERROR) + 
                     rs.get_severity_count(UVM_FATAL);
        
        `uvm_info(get_type_name(), 
                 $sformatf("\n=== FINAL REPORT ==="),
                 UVM_LOW)
        `uvm_info(get_type_name(), 
                 $sformatf("Errors: %0d", error_count),
                 UVM_LOW)
        
        if (error_count == 0) begin
            `uvm_info(get_type_name(), "TEST PASSED", UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), "TEST FAILED")
        end
    endfunction
endclass

// ============================================================================
// Advanced Debug Techniques
// ============================================================================

// Custom Report Catcher
class custom_report_catcher extends uvm_report_catcher;
    int error_count;
    
    function new(string name = "custom_catcher");
        super.new(name);
        error_count = 0;
    endfunction
    
    function action_e catch();
        // Modify or filter messages
        if (get_severity() == UVM_ERROR) begin
            error_count++;
            
            // Demote specific errors to warnings
            if (get_message() == "Address out of range") begin
                set_severity(UVM_WARNING);
                set_message("Address warning (demoted)");
            end
        end
        
        // Add context information
        if (get_verbosity() >= UVM_HIGH) begin
            set_message($sformatf("[%0t] %s", $time, get_message()));
        end
        
        return THROW;  // Continue with modified message
    endfunction
endclass

// Debug Configuration
class debug_config extends uvm_object;
    bit enable_tracing;
    bit enable_assertions;
    bit enable_coverage;
    uvm_verbosity_e verbosity_level;
    
    `uvm_object_utils_begin(debug_config)
        `uvm_field_int(enable_tracing, UVM_ALL_ON)
        `uvm_field_int(enable_assertions, UVM_ALL_ON)
        `uvm_field_int(enable_coverage, UVM_ALL_ON)
        `uvm_field_enum(uvm_verbosity_e, verbosity_level, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "debug_config");
        super.new(name);
        enable_tracing = 1;
        enable_assertions = 1;
        enable_coverage = 1;
        verbosity_level = UVM_MEDIUM;
    endfunction
endclass

// ============================================================================
// Top Module
// ============================================================================
module uvm_debug_messaging;
    
    initial begin
        // Set verbosity from command line or here
        // +UVM_VERBOSITY=UVM_HIGH
        // +UVM_VERBOSITY=UVM_DEBUG
        
        // Or programmatically:
        uvm_top.set_report_verbosity_level_hier(UVM_HIGH);
        
        // Install custom report catcher
        custom_report_catcher catcher = new("catcher");
        uvm_report_cb::add(null, catcher);  // Apply to all components
        
        // Run test
        run_test("debug_test");
    end
    
endmodule

/*
 * UVM DEBUG MESSAGING:
 * 
 * SEVERITY LEVELS:
 * UVM_FATAL:   Simulation stops immediately
 * UVM_ERROR:   Test fails, simulation continues
 * UVM_WARNING: Potential issue, no failure
 * UVM_INFO:    Informational message
 * 
 * VERBOSITY LEVELS:
 * UVM_NONE:   0 (always print)
 * UVM_LOW:    100
 * UVM_MEDIUM: 200 (default)
 * UVM_HIGH:   300
 * UVM_FULL:   400
 * UVM_DEBUG:  500
 * 
 * MACROS:
 * `uvm_fatal(ID, MSG)
 * `uvm_error(ID, MSG)
 * `uvm_warning(ID, MSG)
 * `uvm_info(ID, MSG, VERBOSITY)
 * 
 * SETTING VERBOSITY:
 * 
 * Command line:
 * +UVM_VERBOSITY=UVM_HIGH
 * +UVM_VERBOSITY=UVM_DEBUG
 * 
 * Programmatically:
 * set_report_verbosity_level(UVM_HIGH);
 * set_report_verbosity_level_hier(UVM_HIGH);
 * 
 * Per component:
 * comp.set_report_verbosity_level(UVM_DEBUG);
 * 
 * MESSAGE FILTERING:
 * 
 * By ID:
 * set_report_id_verbosity("DRIVER", UVM_HIGH);
 * set_report_id_action("ERROR_ID", UVM_NO_ACTION);
 * 
 * By severity:
 * set_report_severity_action(UVM_WARNING, UVM_DISPLAY);
 * 
 * FILE OUTPUT:
 * set_report_default_file(file_handle);
 * 
 * REPORT CATCHER:
 * - Intercept messages
 * - Modify severity
 * - Filter messages
 * - Add context
 * - Custom formatting
 * 
 * class my_catcher extends uvm_report_catcher;
 *     function action_e catch();
 *         // Modify message
 *         set_severity(UVM_WARNING);
 *         return THROW;
 *     endfunction
 * endclass
 * 
 * uvm_report_cb::add(null, catcher);
 * 
 * DEBUGGING STRATEGY:
 * 
 * 1. Development:
 *    - UVM_HIGH for detailed logs
 *    - Enable all components
 * 
 * 2. Debug:
 *    - UVM_DEBUG for specific component
 *    - Use report catchers
 *    - Filter by ID
 * 
 * 3. Regression:
 *    - UVM_LOW for minimal output
 *    - Errors only
 *    - Fast execution
 * 
 * BEST PRACTICES:
 * 
 * 1. Use meaningful IDs (get_type_name())
 * 2. Appropriate verbosity levels
 * 3. Include context in messages
 * 4. Use $sformatf for formatted output
 * 5. Don't overuse UVM_DEBUG
 * 6. Filter in regression
 * 
 * COMMON PATTERNS:
 * 
 * 1. Transaction Tracking:
 * `uvm_info(get_type_name(), 
 *          $sformatf("TXN#%0d: %s", id, tr.convert2string()),
 *          UVM_HIGH)
 * 
 * 2. Phase Entry:
 * `uvm_info(get_type_name(), 
 *          $sformatf("%s started", phase.get_name()),
 *          UVM_MEDIUM)
 * 
 * 3. Conditional Debug:
 * if (debug_enable)
 *     `uvm_info("DEBUG", $sformatf(...), UVM_NONE)
 * 
 * 4. Error with Context:
 * `uvm_error(get_type_name(),
 *           $sformatf("Mismatch at addr 0x%0h: exp=%0h act=%0h",
 *                    addr, expected, actual))
 * 
 * REPORT SERVER:
 * uvm_report_server rs = uvm_report_server::get_server();
 * int errors = rs.get_severity_count(UVM_ERROR);
 * int warnings = rs.get_severity_count(UVM_WARNING);
 * 
 * COMMAND-LINE OPTIONS:
 * +UVM_VERBOSITY=<level>
 * +UVM_TESTNAME=<test>
 * +UVM_TIMEOUT=<time>
 * +UVM_MAX_QUIT_COUNT=<n>
 * +UVM_TR_RECORD
 * 
 * PERFORMANCE:
 * - High verbosity = slower simulation
 * - Filter aggressively in regression
 * - Use file output for detailed logs
 * - Consider binary transaction recording
 * 
 * TIPS:
 * ✓ Start with UVM_MEDIUM
 * ✓ Increase for debug (UVM_HIGH, UVM_DEBUG)
 * ✓ Decrease for regression (UVM_LOW)
 * ✓ Use report catchers for custom formatting
 * ✓ Filter by component and ID
 * ✓ Check error count in report_phase
 */
