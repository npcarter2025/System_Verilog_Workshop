// Operand Isolation - Prevents unnecessary logic toggling
// Gates inputs to logic when output not needed

module operand_isolation_example #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             valid,      // Output will be used
    input  logic [WIDTH-1:0] operand_a,
    input  logic [WIDTH-1:0] operand_b,
    output logic [WIDTH-1:0] result
);

    // ============================================
    // WITHOUT OPERAND ISOLATION (wasteful)
    // ============================================
    
    // Computation happens every cycle, even when not needed
    logic [WIDTH-1:0] result_direct;
    assign result_direct = operand_a + operand_b;
    
    // ============================================
    // WITH OPERAND ISOLATION (power efficient)
    // ============================================
    
    // Gate operands when output not valid
    logic [WIDTH-1:0] a_gated, b_gated;
    
    assign a_gated = valid ? operand_a : '0;
    assign b_gated = valid ? operand_b : '0;
    
    // Computation with gated inputs
    logic [WIDTH-1:0] result_gated;
    assign result_gated = a_gated + b_gated;
    
    // Register output
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            result <= '0;
        else if (valid)
            result <= result_gated;
    end
    
    /* Power savings:
     * - When valid=0, a_gated and b_gated are 0
     * - Adder inputs stable (no toggling)
     * - Saves ~40-60% adder dynamic power
     */

endmodule

// Operand isolation for multiplier
module multiplier_with_isolation #(
    parameter WIDTH = 16
) (
    input  logic             clk,
    input  logic             enable,
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [2*WIDTH-1:0] product
);

    logic [WIDTH-1:0] a_iso, b_iso;
    
    // Isolate operands when not enabled
    assign a_iso = enable ? a : '0;
    assign b_iso = enable ? b : '0;
    
    always_ff @(posedge clk) begin
        if (enable)
            product <= a_iso * b_iso;
    end

endmodule
