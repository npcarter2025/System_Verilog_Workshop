// Isolation Cell - Clamp to High
// Used for active-low signals or when high is the safe state

module iso_cell_high (
    input  logic data_in,
    input  logic iso_en,
    output logic data_out
);

    // When iso_en=1, output forced to 1
    assign data_out = data_in | iso_en;

endmodule

// Vectored version
module iso_cell_high_vec #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0] data_in,
    input  logic             iso_en,
    output logic [WIDTH-1:0] data_out
);

    assign data_out = data_in | {WIDTH{iso_en}};

endmodule
