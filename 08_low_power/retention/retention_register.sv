// Retention Register - Maintains state during power-down
// Saves value before power-down, restores after power-up

module retention_register #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             save,       // Save current value
    input  logic             restore,    // Restore saved value
    input  logic             wen,        // Write enable
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Main register (loses state when powered off)
    logic [WIDTH-1:0] main_reg;
    
    // Retention register (always powered, retains state)
    logic [WIDTH-1:0] retention_reg;
    
    // Main register logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            main_reg <= '0;
        else if (restore)
            main_reg <= retention_reg;
        else if (wen)
            main_reg <= data_in;
    end
    
    // Retention register (saves on command)
    always_ff @(posedge clk) begin
        if (save)
            retention_reg <= main_reg;
    end
    
    assign data_out = main_reg;
    
    /* Power-down sequence:
     * 1. Assert 'save' - copy to retention_reg
     * 2. Power down main domain
     * 3. (main_reg lost, retention_reg preserved)
     * 4. Power up main domain
     * 5. Assert 'restore' - copy back from retention_reg
     */

endmodule

// Simplified auto-retention register
module retention_register_auto #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             retention_mode,
    input  logic             wen,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    logic [WIDTH-1:0] reg_data;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reg_data <= '0;
        else if (!retention_mode && wen)
            reg_data <= data_in;
    end
    
    assign data_out = reg_data;

endmodule
