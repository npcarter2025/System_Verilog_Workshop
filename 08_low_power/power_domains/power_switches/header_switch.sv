// Header Power Switch - PMOS between VDD and virtual VDD
// Controls power to entire domain

module header_switch (
    input  logic vdd,           // Real power supply
    input  logic sleep_n,       // Active-low sleep control
    output logic vdd_switched   // Virtual VDD to domain
);

    // Behavioral model of PMOS power switch
    // Real implementation uses large PMOS transistors
    
    // When sleep_n=0 (sleep), switch OFF
    // When sleep_n=1 (active), switch ON
    assign vdd_switched = sleep_n ? vdd : 1'bz;
    
    /* Physical implementation:
     *        VDD
     *         |
     *      ___▽___
     *     |       |  PMOS
     *     |  ◡   |  (sleep_n controls gate)
     *     |_____|
     *         |
     *    vdd_switched (to power domain)
     */

endmodule

// Multi-stage power switch with rush current control
module header_switch_staged #(
    parameter NUM_STAGES = 4
) (
    input  logic       vdd,
    input  logic [NUM_STAGES-1:0] sleep_n_stages,
    output logic       vdd_switched
);

    // Turn on switches sequentially to limit in-rush current
    logic [NUM_STAGES-1:0] switch_on;
    
    genvar i;
    generate
        for (i = 0; i < NUM_STAGES; i++) begin : gen_stages
            assign switch_on[i] = sleep_n_stages[i] ? vdd : 1'bz;
        end
    endgenerate
    
    // Combined output
    assign vdd_switched = |switch_on ? vdd : 1'bz;

endmodule
