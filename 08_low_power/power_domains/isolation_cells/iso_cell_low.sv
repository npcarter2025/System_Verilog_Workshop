// Isolation Cell - Clamp to Low
// Prevents unknown values from powered-off domain

module iso_cell_low (
    input  logic data_in,    // Input from potentially powered-off domain
    input  logic iso_en,     // Isolation enable (1 = isolate, 0 = pass through)
    output logic data_out    // Isolated output
);

    // When iso_en=1, output forced to 0
    // When iso_en=0, data passes through
    assign data_out = data_in & ~iso_en;

endmodule

// Vectored isolation to low
module iso_cell_low_vec #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0] data_in,
    input  logic             iso_en,
    output logic [WIDTH-1:0] data_out
);

    assign data_out = data_in & {WIDTH{~iso_en}};

endmodule
