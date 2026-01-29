// FIFO with State Retention
// Retains FIFO state during power-down

module retention_fifo #(
    parameter DEPTH = 16,
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             save,
    input  logic             restore,
    input  logic             wr_en,
    input  logic [WIDTH-1:0] wr_data,
    input  logic             rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic             full,
    output logic             empty
);

    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    // Main FIFO storage
    logic [WIDTH-1:0] mem [DEPTH];
    logic [ADDR_WIDTH:0] wr_ptr;
    logic [ADDR_WIDTH:0] rd_ptr;
    
    // Retention storage
    logic [WIDTH-1:0] mem_retention [DEPTH];
    logic [ADDR_WIDTH:0] wr_ptr_retention;
    logic [ADDR_WIDTH:0] rd_ptr_retention;
    
    // FIFO logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
            rd_ptr <= '0;
        end else if (restore) begin
            wr_ptr <= wr_ptr_retention;
            rd_ptr <= rd_ptr_retention;
            for (int i = 0; i < DEPTH; i++)
                mem[i] <= mem_retention[i];
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
            if (rd_en && !empty)
                rd_ptr <= rd_ptr + 1;
        end
    end
    
    // Save to retention storage
    always_ff @(posedge clk) begin
        if (save) begin
            wr_ptr_retention <= wr_ptr;
            rd_ptr_retention <= rd_ptr;
            for (int i = 0; i < DEPTH; i++)
                mem_retention[i] <= mem[i];
        end
    end
    
    assign rd_data = mem[rd_ptr[ADDR_WIDTH-1:0]];
    assign full = (wr_ptr[ADDR_WIDTH] != rd_ptr[ADDR_WIDTH]) &&
                  (wr_ptr[ADDR_WIDTH-1:0] == rd_ptr[ADDR_WIDTH-1:0]);
    assign empty = (wr_ptr == rd_ptr);

endmodule
