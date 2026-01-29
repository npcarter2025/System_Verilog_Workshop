// Level Shifter - High Voltage to Low Voltage
// Converts signal from high Vdd domain to low Vdd domain

module level_shifter_down (
    input  logic vdd_high,   // High voltage supply
    input  logic vdd_low,    // Low voltage supply
    input  logic vss,        // Ground
    input  logic data_in,    // Input from high-V domain
    output logic data_out    // Output to low-V domain
);

    // Simplified behavioral model
    // Real implementation uses level shifting circuit
    
    assign data_out = data_in;
    
    // In real design:
    // - Input swings from 0 to vdd_high
    // - Output swings from 0 to vdd_low
    // - Simpler than up-shifter (passive divider possible)
    // - Must handle overvoltage protection

endmodule

// Level shifter with enable
module level_shifter_down_en (
    input  logic data_in,
    input  logic enable,
    output logic data_out
);

    assign data_out = enable ? data_in : 1'b0;

endmodule

// Bidirectional level shifter
module level_shifter_bidir (
    input  logic vdd_high,
    input  logic vdd_low,
    input  logic dir,        // 0=high->low, 1=low->high
    inout  logic data_io_high,
    inout  logic data_io_low
);

    // Bidirectional level shifting
    assign data_io_low  = (dir == 0) ? data_io_high : 1'bz;
    assign data_io_high = (dir == 1) ? data_io_low  : 1'bz;

endmodule
