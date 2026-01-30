// ============================================================================
// simple_tb.sv - Basic Non-UVM Testbench
// ============================================================================
// This demonstrates a simple, traditional testbench without UVM
// ============================================================================

// ============================================================================
// Simple DUT: Adder
// ============================================================================
module adder (
    input  logic clk,
    input  logic rst_n,
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic valid_in,
    output logic [8:0] sum,
    output logic valid_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sum <= 9'h0;
            valid_out <= 1'b0;
        end else begin
            if (valid_in) begin
                sum <= a + b;
                valid_out <= 1'b1;
            end else begin
                valid_out <= 1'b0;
            end
        end
    end
endmodule

// ============================================================================
// Simple Testbench
// ============================================================================
module simple_tb;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // DUT signals
    logic [7:0] a;
    logic [7:0] b;
    logic valid_in;
    logic [8:0] sum;
    logic valid_out;
    
    // Test variables
    int test_count;
    int pass_count;
    int fail_count;
    
    // DUT instantiation
    adder dut (
        .clk(clk),
        .rst_n(rst_n),
        .a(a),
        .b(b),
        .valid_in(valid_in),
        .sum(sum),
        .valid_out(valid_out)
    );
    
    // Clock generation (100MHz, 10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset generation
    task reset_dut();
        $display("[%0t] Resetting DUT...", $time);
        rst_n = 0;
        a = 0;
        b = 0;
        valid_in = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        $display("[%0t] Reset complete", $time);
    endtask
    
    // Drive inputs
    task drive(input logic [7:0] val_a, input logic [7:0] val_b);
        @(posedge clk);
        a <= val_a;
        b <= val_b;
        valid_in <= 1'b1;
        @(posedge clk);
        valid_in <= 1'b0;
        $display("[%0t] Drove: a=%0d, b=%0d", $time, val_a, val_b);
    endtask
    
    // Check result
    task check_result(input logic [8:0] expected);
        @(posedge clk);
        wait(valid_out == 1'b1);
        
        test_count++;
        
        if (sum == expected) begin
            $display("[%0t] PASS: Test #%0d - Expected=%0d, Got=%0d", 
                    $time, test_count, expected, sum);
            pass_count++;
        end else begin
            $display("[%0t] FAIL: Test #%0d - Expected=%0d, Got=%0d", 
                    $time, test_count, expected, sum);
            fail_count++;
        end
    endtask
    
    // Complete test (drive + check)
    task test_add(input logic [7:0] val_a, input logic [7:0] val_b);
        logic [8:0] expected_sum;
        expected_sum = val_a + val_b;
        
        fork
            drive(val_a, val_b);
            check_result(expected_sum);
        join
    endtask
    
    // Random test
    task random_test(int num_tests);
        logic [7:0] rand_a, rand_b;
        
        $display("\n=== Running %0d Random Tests ===", num_tests);
        
        repeat(num_tests) begin
            rand_a = $urandom_range(0, 255);
            rand_b = $urandom_range(0, 255);
            test_add(rand_a, rand_b);
        end
    endtask
    
    // Directed tests
    task directed_tests();
        $display("\n=== Running Directed Tests ===");
        
        // Test 1: Simple addition
        test_add(8'd5, 8'd3);
        
        // Test 2: Zero operands
        test_add(8'd0, 8'd0);
        
        // Test 3: Max values
        test_add(8'd255, 8'd255);
        
        // Test 4: Overflow
        test_add(8'd200, 8'd100);
        
        // Test 5: One operand zero
        test_add(8'd10, 8'd0);
        test_add(8'd0, 8'd10);
    endtask
    
    // Corner case tests
    task corner_case_tests();
        $display("\n=== Running Corner Case Tests ===");
        
        // Minimum values
        test_add(8'd0, 8'd0);
        
        // Maximum values
        test_add(8'd255, 8'd255);
        
        // Powers of 2
        test_add(8'd1, 8'd1);
        test_add(8'd2, 8'd2);
        test_add(8'd4, 8'd4);
        test_add(8'd8, 8'd8);
        test_add(8'd16, 8'd16);
        test_add(8'd32, 8'd32);
        test_add(8'd64, 8'd64);
        test_add(8'd128, 8'd128);
        
        // Boundary values
        test_add(8'd127, 8'd1);
        test_add(8'd254, 8'd1);
    endtask
    
    // Back-to-back tests
    task back_to_back_test();
        $display("\n=== Running Back-to-Back Tests ===");
        
        // No idle cycles between operations
        fork
            begin
                drive(8'd10, 8'd20);
                drive(8'd30, 8'd40);
                drive(8'd50, 8'd60);
            end
            begin
                check_result(9'd30);
                check_result(9'd70);
                check_result(9'd110);
            end
        join
    endtask
    
    // Final report
    task final_report();
        $display("\n");
        $display("===========================================");
        $display("           FINAL TEST REPORT");
        $display("===========================================");
        $display("Total Tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("Pass Rate:    %0.2f%%", 
                real'(pass_count) * 100.0 / real'(test_count));
        $display("===========================================");
        
        if (fail_count == 0) begin
            $display("TEST PASSED!");
        end else begin
            $display("TEST FAILED!");
        end
        $display("===========================================\n");
    endtask
    
    // Main test sequence
    initial begin
        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        $display("\n");
        $display("===========================================");
        $display("      SIMPLE TESTBENCH STARTING");
        $display("===========================================\n");
        
        // Reset
        reset_dut();
        
        // Run test suites
        directed_tests();
        corner_case_tests();
        back_to_back_test();
        random_test(20);
        
        // Wait for completion
        #1000;
        
        // Report
        final_report();
        
        // Finish
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #100000;
        $display("\n[ERROR] Test timeout!");
        final_report();
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("simple_tb.vcd");
        $dumpvars(0, simple_tb);
    end
    
    // Monitor (optional - displays activity)
    always @(posedge clk) begin
        if (valid_out) begin
            $display("[%0t] OUTPUT: sum=%0d", $time, sum);
        end
    end
    
endmodule

/*
 * SIMPLE TESTBENCH STRUCTURE:
 * 
 * COMPONENTS:
 * 1. DUT instantiation
 * 2. Clock generation
 * 3. Reset logic
 * 4. Stimulus generation
 * 5. Response checking
 * 6. Reporting
 * 
 * BASIC PATTERN:
 * module tb;
 *     // 1. Declare signals
 *     logic clk, rst_n;
 *     logic [7:0] data;
 *     
 *     // 2. Instantiate DUT
 *     dut u_dut(.*);
 *     
 *     // 3. Clock generation
 *     initial begin
 *         clk = 0;
 *         forever #5 clk = ~clk;
 *     end
 *     
 *     // 4. Reset
 *     initial begin
 *         rst_n = 0;
 *         #50 rst_n = 1;
 *     end
 *     
 *     // 5. Test stimulus
 *     initial begin
 *         @(posedge rst_n);
 *         // Drive inputs
 *         // Check outputs
 *         #1000 $finish;
 *     end
 * endmodule
 * 
 * ADVANTAGES:
 * + Simple to understand
 * + Fast to write
 * + No dependencies
 * + Good for small designs
 * + Direct control
 * 
 * DISADVANTAGES:
 * - Not reusable
 * - Hard to maintain
 * - No abstraction
 * - Limited scalability
 * - Manual checking
 * 
 * WHEN TO USE:
 * - Quick validation
 * - Small modules
 * - Learning/teaching
 * - Proof of concept
 * - Simple regression
 * 
 * TASKS AND FUNCTIONS:
 * task drive_data(input logic [7:0] d);
 *     @(posedge clk);
 *     data <= d;
 * endtask
 * 
 * function bit check_result(logic [7:0] expected);
 *     return (output_data == expected);
 * endfunction
 * 
 * TEST ORGANIZATION:
 * 1. Directed tests (known values)
 * 2. Corner cases (boundary values)
 * 3. Random tests (constrained random)
 * 4. Back-to-back tests (no idle)
 * 5. Stress tests (max throughput)
 * 
 * CHECKING METHODS:
 * 
 * 1. Inline checks:
 * if (output != expected)
 *     $error("Mismatch!");
 * 
 * 2. Assertion:
 * assert (output == expected)
 *     else $error("Mismatch!");
 * 
 * 3. Task-based:
 * task check(input exp);
 *     if (output != exp) $error();
 * endtask
 * 
 * RANDOM STIMULUS:
 * logic [7:0] rand_val;
 * rand_val = $urandom_range(0, 255);
 * rand_val = $random;  // Signed random
 * 
 * TIMING CONTROL:
 * @(posedge clk);       // Wait for clock edge
 * #10;                  // Wait 10 time units
 * repeat(5) @(clk);     // Wait 5 clock cycles
 * wait(signal == 1);    // Wait for condition
 * 
 * REPORTING:
 * $display("message");
 * $display("[%0t] msg", $time);
 * $error("error message");
 * $warning("warning");
 * $fatal("fatal error");
 * 
 * BEST PRACTICES:
 * 1. Use tasks for reusable operations
 * 2. Separate reset into task
 * 3. Track pass/fail counts
 * 4. Print timestamps
 * 5. Include timeout
 * 6. Dump waveforms
 * 7. Final report
 * 8. Use meaningful names
 * 
 * IMPROVEMENTS:
 * - Add classes for transactions
 * - Use mailboxes for communication
 * - Separate generator/driver/monitor
 * - Add scoreboard
 * - Add coverage
 * → Eventually leads to UVM!
 * 
 * DEBUGGING:
 * - Add $display statements
 * - Dump waveforms ($dumpvars)
 * - Use assertions
 * - Check each stage
 * - Simplify stimulus
 * 
 * COMMON MISTAKES:
 * ❌ No reset
 * ❌ Race conditions
 * ❌ No timeout
 * ❌ Poor error messages
 * ❌ No waveform dump
 * ✅ Always reset
 * ✅ Use @(posedge clk)
 * ✅ Add timeout
 * ✅ Descriptive errors
 * ✅ Dump waveforms
 */
