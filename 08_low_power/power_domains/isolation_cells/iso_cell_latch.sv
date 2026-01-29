// Isolation Cell with Latch
// Latches and holds the last valid value when domain powers off

module iso_cell_latch (
    input  logic clk,
    input  logic data_in,
    input  logic iso_en,     // 1 = isolate (latch last value)
    output logic data_out
);

    logic data_latched;
    
    // Latch last valid value before isolation
    always_latch begin
        if (!iso_en)
            data_latched <= data_in;
    end
    
    // Output latched value during isolation
    assign data_out = iso_en ? data_latched : data_in;

endmodule

// Vectored latch-based isolation
module iso_cell_latch_vec #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic [WIDTH-1:0] data_in,
    input  logic             iso_en,
    output logic [WIDTH-1:0] data_out
);

    logic [WIDTH-1:0] data_latched;
    
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_latch
            always_latch begin
                if (!iso_en)
                    data_latched[i] <= data_in[i];
            end
        end
    endgenerate
    
    assign data_out = iso_en ? data_latched : data_in;

endmodule

// Clocked latch isolation (safer)
module iso_cell_latch_clocked (
    input  logic clk,
    input  logic data_in,
    input  logic iso_en,
    output logic data_out
);

    logic data_saved;
    
    // Save data on rising edge before isolation
    always_ff @(posedge clk) begin
        if (!iso_en)
            data_saved <= data_in;
    end
    
    assign data_out = iso_en ? data_saved : data_in;

endmodule
