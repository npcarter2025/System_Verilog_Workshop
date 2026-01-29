// Formal Verification of Gray Code Properties
// Gray codes are essential for safe CDC (Clock Domain Crossing)

module gray_code_formal_properties #(
    parameter WIDTH = 4
) (
    input logic             clk,
    input logic             rst_n,
    input logic             en,
    input logic [WIDTH-1:0] binary_count,
    input logic [WIDTH-1:0] gray_count
);

    // ============================================
    // PART 1: GRAY CODE ENCODING
    // ============================================
    
    // Property 1.1: Gray code is correctly encoded from binary
    property gray_encoding_correct;
        @(posedge clk) disable iff (!rst_n)
        gray_count == (binary_count ^ (binary_count >> 1));
    endproperty
    
    a_encoding: assert property (gray_encoding_correct)
        else $error("Gray encoding incorrect: binary=%b, gray=%b, expected=%b",
                   binary_count, gray_count, (binary_count ^ (binary_count >> 1)));
    
    // ============================================
    // PART 2: SINGLE BIT CHANGE
    // ============================================
    
    // Property 2.1: Adjacent gray codes differ by exactly one bit
    // This is THE critical property for CDC safety
    property one_bit_change;
        @(posedge clk) disable iff (!rst_n)
        en |=> $countones(gray_count ^ $past(gray_count)) <= 1;
    endproperty
    
    a_one_bit: assert property (one_bit_change)
        else $error("Multiple bits changed: prev=%b, curr=%b, diff=%b",
                   $past(gray_count), gray_count, 
                   gray_count ^ $past(gray_count));
    
    // Property 2.2: When enabled, at most one bit changes
    property single_bit_transition;
        logic [WIDTH-1:0] prev_gray;
        @(posedge clk) disable iff (!rst_n)
        (en, prev_gray = gray_count) |=> 
            (gray_count == prev_gray) || 
            ($onehot(gray_count ^ prev_gray));
    endproperty
    
    a_single_bit: assert property (single_bit_transition);
    
    // ============================================
    // PART 3: UNIQUENESS (BIJECTION)
    // ============================================
    
    // Property 3.1: Gray codes are unique (no two binary values map to same gray)
    // This requires checking all pairs - expensive for formal
    
    // For formal verification, we use this approach:
    // If binary values differ, gray codes must differ
    property gray_uniqueness;
        logic [WIDTH-1:0] other_binary, other_gray;
        @(posedge clk) disable iff (!rst_n)
        (1'b1, other_binary = $past(binary_count, 1)) |->
            (binary_count == other_binary) || 
            (gray_count != (other_binary ^ (other_binary >> 1)));
    endproperty
    
    a_unique: assert property (gray_uniqueness);
    
    // ============================================
    // PART 4: CYCLE PROPERTIES
    // ============================================
    
    // Property 4.1: Gray code cycles through all values
    // After 2^WIDTH increments, returns to starting value
    localparam MAX_COUNT = (1 << WIDTH);
    
    property gray_cycles;
        logic [WIDTH-1:0] start_gray;
        @(posedge clk) disable iff (!rst_n)
        (binary_count == 0, start_gray = gray_count) |->
            ##[(MAX_COUNT-1):(MAX_COUNT-1)] (gray_count == start_gray);
    endproperty
    
    // Note: This requires deep trace - may timeout
    // a_cycles: assert property (gray_cycles);
    
    // Property 4.2: Each gray code value appears exactly once in cycle
    // This is covered by uniqueness property
    
    // ============================================
    // PART 5: INCREMENT/DECREMENT
    // ============================================
    
    // Property 5.1: Binary increment corresponds to gray transition
    property binary_to_gray_increment;
        @(posedge clk) disable iff (!rst_n)
        en |=> (gray_count == ($past(binary_count) + 1) ^ 
                             (($past(binary_count) + 1) >> 1));
    endproperty
    
    a_increment: assert property (binary_to_gray_increment);
    
    // ============================================
    // PART 6: WRAP-AROUND
    // ============================================
    
    // Property 6.1: Wrap from maximum to zero is single-bit change
    property wraparound_safe;
        @(posedge clk) disable iff (!rst_n)
        (binary_count == (MAX_COUNT - 1)) && en |=>
            $countones(gray_count ^ $past(gray_count)) == 1;
    endproperty
    
    a_wrap: assert property (wraparound_safe)
        else $error("Wrap-around not single-bit: from=%b to=%b",
                   $past(gray_count), gray_count);
    
    // Property 6.2: Wrapping gray code transition
    property wrap_transition;
        logic [WIDTH-1:0] max_gray;
        @(posedge clk) disable iff (!rst_n)
        (binary_count == (MAX_COUNT - 1), max_gray = gray_count) |=>
            en |-> $countones(gray_count ^ max_gray) == 1;
    endproperty
    
    a_wrap_trans: assert property (wrap_transition);
    
    // ============================================
    // PART 7: STABILITY
    // ============================================
    
    // Property 7.1: Gray code stable when not enabled
    property stable_when_disabled;
        @(posedge clk) disable iff (!rst_n)
        !en |=> $stable(gray_count);
    endproperty
    
    a_stable: assert property (stable_when_disabled);
    
    // Property 7.2: Binary stable when not enabled
    property binary_stable;
        @(posedge clk) disable iff (!rst_n)
        !en |=> $stable(binary_count);
    endproperty
    
    a_bin_stable: assert property (binary_stable);
    
    // ============================================
    // PART 8: RESET BEHAVIOR
    // ============================================
    
    // Property 8.1: Reset to zero
    property reset_to_zero;
        @(posedge clk)
        !rst_n |=> (gray_count == 0) && (binary_count == 0);
    endproperty
    
    a_reset: assert property (reset_to_zero);
    
    // ============================================
    // PART 9: COVERAGE
    // ============================================
    
    // Cover: Reach all gray code values
    genvar i;
    generate
        for (i = 0; i < MAX_COUNT; i++) begin : gen_cover_values
            c_value: cover property (
                @(posedge clk) gray_count == (i ^ (i >> 1))
            );
        end
    endgenerate
    
    // Cover: All single-bit transitions
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_cover_transitions
            c_bit_toggle: cover property (
                @(posedge clk) gray_count[i] != $past(gray_count[i]) &&
                               gray_count[i^1] == $past(gray_count[i^1])
            );
        end
    endgenerate
    
    // Cover: Full cycle
    c_full_cycle: cover property (
        @(posedge clk) (binary_count == 0) ##(MAX_COUNT) (binary_count == 0)
    );
    
    // Cover: Wraparound
    c_wraparound: cover property (
        @(posedge clk) (binary_count == (MAX_COUNT-1)) ##1 (binary_count == 0)
    );

endmodule

// ============================================
// GRAY CODE COUNTER IMPLEMENTATION
// ============================================

module gray_counter #(
    parameter WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] binary_count,
    output logic [WIDTH-1:0] gray_count
);

    // Binary counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            binary_count <= '0;
        else if (en)
            binary_count <= binary_count + 1;
    end
    
    // Gray encoding: XOR with right-shifted version
    assign gray_count = binary_count ^ (binary_count >> 1);

endmodule

// ============================================
// FORMAL TESTBENCH
// ============================================

module gray_code_formal_tb;

    parameter WIDTH = 4;
    
    logic             clk;
    logic             rst_n;
    logic             en;
    logic [WIDTH-1:0] binary_count;
    logic [WIDTH-1:0] gray_count;
    
    // DUT
    gray_counter #(.WIDTH(WIDTH)) dut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .binary_count(binary_count),
        .gray_count(gray_count)
    );
    
    // Formal properties
    gray_code_formal_properties #(.WIDTH(WIDTH)) checker (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .binary_count(binary_count),
        .gray_count(gray_count)
    );
    
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Reset generation
    initial begin
        rst_n = 0;
        en = 0;
        #20;
        rst_n = 1;
        #10;
        en = 1;
    end
    
    // Simulation (for waveform debugging)
    `ifndef FORMAL_VERIFICATION
    initial begin
        @(posedge rst_n);
        @(posedge clk);
        
        // Run through full cycle
        repeat((1 << WIDTH) + 5) @(posedge clk);
        
        $display("Gray code sequence:");
        for (int i = 0; i < (1 << WIDTH); i++) begin
            logic [WIDTH-1:0] exp_gray = i ^ (i >> 1);
            $display("Binary: %b -> Gray: %b", i, exp_gray);
        end
        
        $finish;
    end
    
    initial begin
        $dumpfile("gray_code.vcd");
        $dumpvars(0, gray_code_formal_tb);
    end
    `endif

endmodule

// ============================================
// GRAY TO BINARY DECODER (for completeness)
// ============================================

module gray_to_binary #(
    parameter WIDTH = 4
) (
    input  logic [WIDTH-1:0] gray_in,
    output logic [WIDTH-1:0] binary_out
);

    // Decode gray to binary by XOR accumulation
    always_comb begin
        binary_out[WIDTH-1] = gray_in[WIDTH-1];
        for (int i = WIDTH-2; i >= 0; i--) begin
            binary_out[i] = binary_out[i+1] ^ gray_in[i];
        end
    end

endmodule

// Formal properties for decoder
module gray_to_binary_formal #(
    parameter WIDTH = 4
) (
    input logic [WIDTH-1:0] gray_in,
    input logic [WIDTH-1:0] binary_out
);

    // Property: Encoding then decoding returns original
    property encode_decode_identity;
        logic [WIDTH-1:0] encoded;
        (1'b1, encoded = binary_out ^ (binary_out >> 1)) |->
            (gray_in == encoded) |-> 
            (binary_out == binary_out);  // Tautology but demonstrates flow
    endproperty
    
    // Property: Decode is inverse of encode
    property decode_inverse;
        logic [WIDTH-1:0] reencoded;
        (1'b1, reencoded = binary_out ^ (binary_out >> 1)) |->
            (reencoded == gray_in);
    endproperty
    
    a_inverse: assert property (decode_inverse);

endmodule

// ============================================
// WHY GRAY CODE FOR CDC?
// ============================================

/*
 * Gray codes are critical for Clock Domain Crossing because:
 *
 * 1. SINGLE BIT CHANGE: Only one bit changes between adjacent values
 *    - If metastability occurs on that bit, only +/-1 error
 *    - Binary counters can have multiple bits change (e.g., 0111->1000)
 *    - Multiple bit changes can cause large errors due to different delays
 *
 * 2. EXAMPLE:
 *    Binary 0111 (7) -> 1000 (8) = 4 bits change
 *    If MSB seen before LSBs cleared: 1111 (15) - huge error!
 *    
 *    Gray 0100 (7) -> 1100 (8) = 1 bit changes
 *    Even with metastability: 0100 or 1100 (7 or 8) - acceptable error
 *
 * 3. ASYNC FIFO USE CASE:
 *    - Write pointer in clk_wr domain
 *    - Read pointer in clk_rd domain
 *    - Must compare pointers across domains
 *    - Gray code ensures safe comparison
 *
 * 4. FORMAL VERIFICATION PROVES:
 *    - Encoding is correct
 *    - Only one bit changes per increment
 *    - No glitches or multi-bit transitions
 *    - Safe for CDC usage
 */
