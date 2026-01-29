// Dynamic Frequency Divider for DVFS
// Adjusts clock frequency based on performance requirements

module freq_divider_dynamic #(
    parameter MAX_DIV = 16
) (
    input  logic                      clk_in,
    input  logic                      rst_n,
    input  logic [$clog2(MAX_DIV)-1:0] div_ratio,  // 1 to MAX_DIV
    output logic                      clk_out
);

    logic [$clog2(MAX_DIV)-1:0] counter;
    logic clk_divided;
    
    always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
            clk_divided <= 0;
        end else begin
            if (counter >= (div_ratio - 1)) begin
                counter <= '0;
                clk_divided <= ~clk_divided;
            end else begin
                counter <= counter + 1;
            end
        end
    end
    
    // Output divided clock
    assign clk_out = (div_ratio == 1) ? clk_in : clk_divided;

endmodule

// DVFS Controller
module dvfs_controller (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] workload,     // Current workload (0-100%)
    output logic [1:0] perf_mode,    // Performance mode
    output logic [2:0] freq_div      // Frequency divider
);

    // Performance modes
    localparam MODE_HIGH   = 2'b11;  // Full speed
    localparam MODE_MEDIUM = 2'b10;  // Half speed
    localparam MODE_LOW    = 2'b01;  // Quarter speed
    localparam MODE_IDLE   = 2'b00;  // Minimum speed
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            perf_mode <= MODE_LOW;
            freq_div <= 3'd4;
        end else begin
            case (workload)
                8'd0   : begin perf_mode <= MODE_IDLE;   freq_div <= 3'd8; end
                8'd1 : begin perf_mode <= MODE_LOW;    freq_div <= 3'd4; end
                8'd26: begin perf_mode <= MODE_MEDIUM; freq_div <= 3'd2; end
                default: begin perf_mode <= MODE_HIGH;   freq_div <= 3'd1; end
            endcase
        end
    end

endmodule
