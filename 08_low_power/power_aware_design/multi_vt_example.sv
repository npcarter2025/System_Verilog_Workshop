// Multi-Vt (Threshold Voltage) Design Example
// Shows usage of High-Vt and Low-Vt cells for power/performance tradeoff

/*
 * Multi-Vt Design Concepts:
 * 
 * Low-Vt (LVT) cells:
 *   - Fast switching (low threshold)
 *   - High leakage current
 *   - Use in critical timing paths
 *
 * Standard-Vt (SVT) cells:
 *   - Balanced speed and leakage
 *   - Default choice for most logic
 *
 * High-Vt (HVT) cells:
 *   - Slow switching (high threshold)
 *   - Very low leakage
 *   - Use in non-critical paths
 *
 * Power savings: 30-50% leakage reduction
 * Area overhead: None (same cell size)
 * Performance: Critical paths use LVT, others use HVT
 */

module multi_vt_design_example (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] data_in,
    input  logic        valid_in,
    output logic [31:0] data_out,
    output logic        valid_out
);

    // Critical path: Use Low-Vt cells
    // synthesis translate_off
    // synopsys dc_script_begin
    // set_threshold_voltage_group -name LVT critical_path_logic
    // synopsys dc_script_end
    // synthesis translate_on
    
    logic [31:0] critical_result;
    assign critical_result = data_in + 32'd100;  // Fast adder
    
    // Non-critical path: Use High-Vt cells
    // synthesis translate_off
    // synopsys dc_script_begin
    // set_threshold_voltage_group -name HVT control_logic
    // synopsys dc_script_end
    // synthesis translate_on
    
    logic valid_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            valid_reg <= 1'b0;
        else
            valid_reg <= valid_in;
    end
    
    // Output register: Standard-Vt
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= '0;
            valid_out <= 1'b0;
        end else begin
            data_out <= critical_result;
            valid_out <= valid_reg;
        end
    end

endmodule

/*
 * Synthesis Constraints (SDC):
 *
 * # Set voltage groups
 * set_voltage LVT -object_list [get_cells critical_path*] -voltage 1.1
 * set_voltage HVT -object_list [get_cells control_logic*] -voltage 0.9
 *
 * # Map to library cells
 * set_threshold_voltage_group LVT [get_lib_cells *_LVT]
 * set_threshold_voltage_group HVT [get_lib_cells *_HVT]
 *
 * # Leakage optimization
 * set_leakage_optimization true
 * optimize_power -leakage
 *
 * Typical Results:
 *   - 40% leakage reduction
 *   - <5% area increase
 *   - Same performance on critical paths
 */
