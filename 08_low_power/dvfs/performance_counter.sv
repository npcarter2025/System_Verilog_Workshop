// Performance Counter for DVFS
// Tracks activity to determine optimal operating point

module performance_counter (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        activity,     // High when work is being done
    output logic [15:0] util_percent  // Utilization percentage
);

    logic [15:0] active_count;
    logic [15:0] total_count;
    logic [15:0] utilization;
    
    // Count active and total cycles
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            active_count <= 0;
            total_count <= 0;
        end else begin
            if (total_count >= 16'd1000) begin
                // Reset every 1000 cycles
                active_count <= activity ? 1 : 0;
                total_count <= 1;
            end else begin
                active_count <= active_count + (activity ? 1 : 0);
                total_count <= total_count + 1;
            end
        end
    end
    
    // Calculate utilization percentage
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            utilization <= 0;
        else if (total_count == 16'd999)
            utilization <= (active_count * 100) / total_count;
    end
    
    assign util_percent = utilization;

endmodule

// Multi-metric performance counter
module performance_counter_multi (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        instr_valid,
    input  logic        cache_miss,
    input  logic        stall,
    output logic [7:0]  ipc,          // Instructions per cycle
    output logic [7:0]  miss_rate,    // Cache miss rate
    output logic [7:0]  stall_rate    // Stall rate
);

    logic [15:0] instr_count, miss_count, stall_count, cycle_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            instr_count <= 0;
            miss_count <= 0;
            stall_count <= 0;
            cycle_count <= 0;
        end else begin
            if (cycle_count >= 16'd1000) begin
                instr_count <= instr_valid ? 1 : 0;
                miss_count <= cache_miss ? 1 : 0;
                stall_count <= stall ? 1 : 0;
                cycle_count <= 1;
            end else begin
                instr_count <= instr_count + (instr_valid ? 1 : 0);
                miss_count <= miss_count + (cache_miss ? 1 : 0);
                stall_count <= stall_count + (stall ? 1 : 0);
                cycle_count <= cycle_count + 1;
            end
        end
    end
    
    // Calculate metrics
    always_ff @(posedge clk) begin
        if (cycle_count == 16'd999) begin
            ipc <= (instr_count * 100) / cycle_count;
            miss_rate <= (miss_count * 100) / cycle_count;
            stall_rate <= (stall_count * 100) / cycle_count;
        end
    end

endmodule
