// Voltage Monitor
// Simple voltage level detector for DVFS

module voltage_monitor #(
    parameter THRESHOLD_LOW  = 16'h3000,
    parameter THRESHOLD_HIGH = 16'h4000
) (
    input  logic [15:0] voltage_adc,
    output logic        voltage_ok,
    output logic        voltage_low,
    output logic        voltage_high
);

    // Compare voltage against thresholds
    assign voltage_low  = (voltage_adc < THRESHOLD_LOW);
    assign voltage_high = (voltage_adc > THRESHOLD_HIGH);
    assign voltage_ok   = !voltage_low && !voltage_high;

endmodule

// Voltage monitor with hysteresis
module voltage_monitor_hysteresis (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] voltage_adc,
    output logic        voltage_ok
);

    parameter THRESHOLD_LOW  = 16'h3000;
    parameter THRESHOLD_HIGH = 16'h3200;
    parameter HYSTERESIS     = 16'h0100;
    
    logic ok_state;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            ok_state <= 1'b0;
        else begin
            if (voltage_adc < THRESHOLD_LOW)
                ok_state <= 1'b0;
            else if (voltage_adc > (THRESHOLD_LOW + HYSTERESIS))
                ok_state <= 1'b1;
        end
    end
    
    assign voltage_ok = ok_state;

endmodule

// Multi-level voltage detector
module voltage_detector_multilevel (
    input  logic [15:0] voltage_adc,
    output logic [2:0]  voltage_level
);

    always_comb begin
        if (voltage_adc < 16'h2000)
            voltage_level = 3'b000;      // Very low
        else if (voltage_adc < 16'h3000)
            voltage_level = 3'b001;      // Low
        else if (voltage_adc < 16'h4000)
            voltage_level = 3'b010;      // Normal
        else if (voltage_adc < 16'h5000)
            voltage_level = 3'b011;      // High
        else
            voltage_level = 3'b100;      // Very high
    end

endmodule
