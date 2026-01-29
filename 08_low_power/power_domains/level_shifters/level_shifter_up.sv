// Level Shifter - Low Voltage to High Voltage
// Converts signal from low Vdd domain to high Vdd domain

module level_shifter_up (
    input  logic vdd_low,    // Low voltage supply
    input  logic vdd_high,   // High voltage supply  
    input  logic vss,        // Ground
    input  logic data_in,    // Input from low-V domain
    output logic data_out    // Output to high-V domain
);

    // Simplified behavioral model
    // Real implementation uses cross-coupled transistors
    
    assign data_out = data_in;
    
    // In real design, level shifter circuit ensures:
    // - Input swings from 0 to vdd_low
    // - Output swings from 0 to vdd_high
    // - No DC current flow
    // - Proper noise margins

endmodule

// Parametrized level shifter
module level_shifter_up_param #(
    parameter V_LOW  = "0.8V",
    parameter V_HIGH = "1.2V"
) (
    input  logic data_in,
    output logic data_out
);

    assign data_out = data_in;
    
    // Assertions for voltage requirements
    initial begin
        $display("Level Shifter: %s -> %s", V_LOW, V_HIGH);
    end

endmodule
