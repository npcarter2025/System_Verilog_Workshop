// Synchronous FIFO Model for Formal Verification
// This is the DUT (Design Under Test)

module sync_fifo #(
    parameter DEPTH = 16,
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    
    // Write interface
    input  logic             push,
    input  logic [WIDTH-1:0] wr_data,
    output logic             full,
    output logic             almost_full,
    
    // Read interface
    input  logic             pop,
    output logic [WIDTH-1:0] rd_data,
    output logic             empty,
    output logic             almost_empty,
    
    // Status
    output logic [$clog2(DEPTH):0] count
);

    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    // Internal memory
    logic [WIDTH-1:0] mem [DEPTH];
    
    // Pointers (one extra bit for full/empty detection)
    logic [ADDR_WIDTH:0] wr_ptr, rd_ptr;
    
    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else if (push && !full) begin
            mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    // Read logic  
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
        end else if (pop && !empty) begin
            rd_ptr <= rd_ptr + 1;
        end
    end
    
    // Read data (combinational read)
    assign rd_data = mem[rd_ptr[ADDR_WIDTH-1:0]];
    
    // Status generation
    assign count = wr_ptr - rd_ptr;
    assign empty = (count == 0);
    assign full = (count == DEPTH);
    assign almost_empty = (count == 1);
    assign almost_full = (count == DEPTH - 1);

endmodule
