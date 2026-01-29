// Footer Power Switch - NMOS between virtual VSS and real VSS  
// Controls ground connection to power domain

module footer_switch (
    input  logic vss,           // Real ground
    input  logic sleep_n,       // Active-low sleep control
    output logic vss_switched   // Virtual VSS to domain
);

    // Behavioral model of NMOS power switch
    // Real implementation uses large NMOS transistors
    
    // When sleep_n=0 (sleep), switch OFF
    // When sleep_n=1 (active), switch ON
    assign vss_switched = sleep_n ? vss : 1'bz;
    
    /* Physical implementation:
     *    vss_switched (from power domain)
     *         |
     *      ___▽___
     *     |       |  NMOS
     *     |  ◡   |  (sleep_n controls gate)
     *     |_____|
     *         |
     *        VSS
     */

endmodule

// Footer switch with controlled wake-up
module footer_switch_controlled (
    input  logic       vss,
    input  logic [3:0] wake_stages,  // Gradual wake-up
    output logic       vss_switched
);

    // Turn on switches gradually to limit in-rush current
    logic [3:0] switch_on;
    
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_stages
            assign switch_on[i] = wake_stages[i] ? vss : 1'bz;
        end
    endgenerate
    
    assign vss_switched = |wake_stages ? vss : 1'bz;

endmodule

// Combined header and footer switches
module dual_power_switch (
    input  logic vdd,
    input  logic vss,
    input  logic sleep_n,
    output logic vdd_switched,
    output logic vss_switched
);

    // Header (PMOS) for VDD
    assign vdd_switched = sleep_n ? vdd : 1'bz;
    
    // Footer (NMOS) for VSS  
    assign vss_switched = sleep_n ? vss : 1'bz;
    
    // Using both provides better isolation

endmodule
