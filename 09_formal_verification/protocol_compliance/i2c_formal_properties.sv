// Formal Properties for I2C (Inter-Integrated Circuit) Protocol
// I2C is a multi-master, multi-slave serial bus protocol

module i2c_formal_properties (
    input logic scl,        // Clock line (open-drain)
    input logic sda,        // Data line (open-drain)
    input logic scl_out,    // What master/slave drives (0=pull low, 1=release)
    input logic sda_out     // What master/slave drives (0=pull low, 1=release)
);

    // ============================================
    // I2C PROTOCOL BASICS
    // ============================================
    // - Open-drain: Multiple devices can pull low, but only pull-ups drive high
    // - START: SDA falls while SCL high
    // - STOP: SDA rises while SCL high
    // - Data valid when SCL high, changes when SCL low
    // - ACK/NACK: 9th bit (0=ACK, 1=NACK)
    
    // ============================================
    // START CONDITION
    // ============================================
    
    // START: SDA falls while SCL is high
    sequence start_condition;
        (scl && sda) ##1 (scl && !sda);
    endsequence
    
    property start_valid;
        start_condition;
    endproperty
    
    c_start: cover property (@(posedge scl or negedge sda) start_condition);
    
    // Property: START only when bus idle (both high) or after STOP
    logic bus_busy;
    
    always_ff @(start_condition or negedge scl) begin
        if (start_condition.triggered)
            bus_busy <= 1;
        // Cleared by STOP condition
    end
    
    // ============================================
    // STOP CONDITION
    // ============================================
    
    // STOP: SDA rises while SCL is high
    sequence stop_condition;
        (scl && !sda) ##1 (scl && sda);
    endsequence
    
    c_stop: cover property (@(posedge scl or posedge sda) stop_condition);
    
    // Property: STOP releases bus
    property stop_releases_bus;
        @(posedge sda)
        (scl && $past(!sda)) |=> !bus_busy;
    endproperty
    
    // ============================================
    // DATA VALIDITY
    // ============================================
    
    // Property: SDA stable while SCL high (except START/STOP)
    property sda_stable_during_scl_high;
        @(posedge scl)
        !start_condition && !stop_condition |-> 
            ##1 ($stable(sda) throughout (scl[->1]));
    endproperty
    
    a_sda_stable: assert property (sda_stable_during_scl_high)
        else $error("I2C VIOLATION: SDA changed while SCL high (not START/STOP)");
    
    // Property: SDA changes only when SCL low
    property sda_changes_on_scl_low;
        @(posedge sda or negedge sda)
        !start_condition && !stop_condition |-> !scl;
    endproperty
    
    a_sda_timing: assert property (sda_changes_on_scl_low)
        else $error("I2C VIOLATION: SDA changed while SCL high");
    
    // ============================================
    // CLOCK STRETCHING
    // ============================================
    
    // Property: Slave can hold SCL low (clock stretching)
    // Master must wait for SCL to go high before continuing
    
    property clock_stretch_respected;
        @(negedge scl_out)  // Master tries to release SCL
        scl_out |-> ##[0:100] scl;  // Wait for actual SCL high
    endproperty
    
    // This checks master respects clock stretching
    
    // ============================================
    // BIT TIMING
    // ============================================
    
    // Property: Minimum SCL low time
    property min_scl_low;
        @(negedge scl)
        scl |-> ##[4:$] !scl;  // At least 4 time units low
    endproperty
    
    // Property: Minimum SCL high time
    property min_scl_high;
        @(posedge scl)
        !scl |-> ##[4:$] scl;  // At least 4 time units high
    endproperty
    
    // ============================================
    // BYTE TRANSFER
    // ============================================
    
    // Track byte transfer (8 data bits + 1 ACK bit)
    logic [2:0] bit_count;
    logic in_transfer;
    
    always_ff @(posedge scl or start_condition or stop_condition) begin
        if (start_condition.triggered) begin
            bit_count <= 0;
            in_transfer <= 1;
        end else if (stop_condition.triggered) begin
            in_transfer <= 0;
        end else if (in_transfer && scl) begin
            if (bit_count == 8)
                bit_count <= 0;  // ACK bit done, ready for next byte
            else
                bit_count <= bit_count + 1;
        end
    end
    
    // Property: 9 bits per byte (8 data + 1 ACK)
    property nine_bits_per_byte;
        @(posedge scl)
        in_transfer && (bit_count == 8) |-> 
            ##1 (bit_count == 0);  // Wrap after ACK
    endproperty
    
    // ============================================
    // ACKNOWLEDGE
    // ============================================
    
    // Property: ACK/NACK is 9th bit
    property ack_on_ninth_bit;
        @(posedge scl)
        in_transfer && (bit_count == 8) |-> 
            !$isunknown(sda);  // ACK bit must be defined
    endproperty
    
    a_ack_defined: assert property (ack_on_ninth_bit)
        else $error("I2C VIOLATION: Undefined ACK bit");
    
    // Property: After ACK, either continue or STOP
    property after_ack;
        @(posedge scl)
        in_transfer && (bit_count == 8) |->
            ##[1:10] (bit_count == 0) or stop_condition;
    endproperty
    
    // ============================================
    // ADDRESS PHASE
    // ============================================
    
    // Property: First byte after START is address
    logic [6:0] address;
    logic rw_bit;
    
    // Capture address (7 bits) + R/W bit
    // This would need more state tracking in practice
    
    // ============================================
    // ARBITRATION (Multi-Master)
    // ============================================
    
    // Property: Arbitration - if master drives 1 but sees 0, it lost
    property arbitration_lost;
        @(posedge scl)
        sda_out && !sda |-> ##1 !sda_out;  // Stop driving
    endproperty
    
    a_arb: assert property (arbitration_lost)
        else $error("I2C VIOLATION: Master didn't release after losing arbitration");
    
    // Property: Winner continues, loser stops
    
    // ============================================
    // REPEATED START
    // ============================================
    
    // Property: Repeated START allowed (START without prior STOP)
    sequence repeated_start;
        start_condition ##[9:$] start_condition;
    endsequence
    
    c_repeated_start: cover property (@(posedge scl or negedge sda) repeated_start);
    
    // ============================================
    // BUS IDLE
    // ============================================
    
    // Property: Bus idle = both SDA and SCL high
    property bus_idle_definition;
        !in_transfer |-> (scl && sda);
    endproperty
    
    // ============================================
    // HOLD TIME
    // ============================================
    
    // Property: SDA hold time after SCL falls
    property sda_hold_time;
        @(negedge scl)
        1'b1 |-> ##[0:2] $stable(sda);  // Hold for at least 2 time units
    endproperty
    
    // ============================================
    // SETUP TIME
    // ============================================
    
    // Property: SDA setup time before SCL rises
    property sda_setup_time;
        @(posedge scl)
        $past($stable(sda), 2);  // SDA stable for 2 time units before SCL rise
    endproperty
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Complete byte transfer
    sequence byte_transfer;
        start_condition ##9 stop_condition;
    endsequence
    
    c_byte: cover property (@(posedge scl) byte_transfer);
    
    // Cover: ACK
    c_ack: cover property (
        @(posedge scl) (bit_count == 8) && !sda
    );
    
    // Cover: NACK
    c_nack: cover property (
        @(posedge scl) (bit_count == 8) && sda
    );
    
    // Cover: Clock stretching
    c_stretch: cover property (
        @(negedge scl_out) scl_out && !scl
    );
    
    // Cover: Multi-byte transfer
    c_multi_byte: cover property (
        @(posedge scl) 
        start_condition ##[9:$] (bit_count == 0) ##9 (bit_count == 0)
    );
    
    // ============================================
    // SPEED MODES
    // ============================================
    
    // I2C has multiple speed modes:
    // - Standard: 100 kHz
    // - Fast: 400 kHz
    // - Fast Plus: 1 MHz
    // - High Speed: 3.4 MHz
    
    // Property: Clock frequency within spec (example for 100kHz)
    // This would require actual timing measurement
    
    // ============================================
    // 10-BIT ADDRESSING
    // ============================================
    
    // Property: 10-bit address has special first byte (11110XX)
    // This would require additional state tracking

endmodule

// ============================================
// I2C MASTER FORMAL PROPERTIES
// ============================================

module i2c_master_formal (
    input logic        clk,         // System clock
    input logic        rst_n,
    input logic        scl_out,     // What master drives
    input logic        sda_out,     // What master drives
    input logic        scl,         // Actual bus value
    input logic        sda,         // Actual bus value
    input logic [2:0]  state        // Master FSM state
);

    // Master-specific checks
    
    // Property: Master generates START
    property master_start;
        @(posedge clk) disable iff (!rst_n)
        (state == 3'b001) |-> ##[1:5] (!sda && scl);
    endproperty
    
    // Property: Master generates SCL
    property master_scl_control;
        @(posedge clk) disable iff (!rst_n)
        (state != 3'b000) |-> !$isunknown(scl_out);
    endproperty
    
    a_master_scl: assert property (master_scl_control);
    
    // Property: Master respects slave clock stretching
    property respect_stretch;
        @(posedge clk) disable iff (!rst_n)
        scl_out && !scl |-> ##[1:$] scl before (state == 3'b000);
    endproperty

endmodule

// ============================================
// I2C SLAVE FORMAL PROPERTIES
// ============================================

module i2c_slave_formal (
    input logic       clk,
    input logic       rst_n,
    input logic       scl,
    input logic       sda,
    input logic       sda_out,      // What slave drives
    input logic       addr_match    // Address matches this slave
);

    // Slave-specific checks
    
    // Property: Slave only drives during ACK/data phases
    property slave_drive_timing;
        @(posedge scl) disable iff (!rst_n)
        !sda_out |-> addr_match;  // Only drive if addressed
    endproperty
    
    // Property: Slave can stretch clock (hold SCL low)
    // Slave never drives SCL high (open-drain)
    
    // Property: Slave ACKs when addressed
    property slave_acks_address;
        @(posedge scl) disable iff (!rst_n)
        addr_match |-> ##9 !sda_out;  // Drive ACK
    endproperty

endmodule

// ============================================
// NOTES
// ============================================

/*
 * I2C Protocol Complexity:
 *   - Open-drain makes formal verification challenging
 *   - Multiple masters require arbitration checking
 *   - Clock stretching adds timing dependencies
 *   - START/STOP conditions need special handling
 *
 * Formal Verification Strategy:
 *   1. Verify START/STOP conditions are correct
 *   2. Check data stability during SCL high
 *   3. Verify arbitration logic (multi-master)
 *   4. Check clock stretching respect
 *   5. Verify ACK/NACK handling
 *
 * Common Bugs:
 *   - SDA changing while SCL high (glitches)
 *   - Missing START/STOP detection
 *   - Incorrect bit counting
 *   - Not respecting clock stretching
 *   - Arbitration loss not detected
 */
