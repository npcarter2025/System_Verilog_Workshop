// Memory Power-Down Control
// Controls RAM sleep modes for power savings

module memory_power_down #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 1024
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    sleep_mode,
    input  logic                    wr_en,
    input  logic [ADDR_WIDTH-1:0]   addr,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic [DATA_WIDTH-1:0]   rd_data
);

    logic [DATA_WIDTH-1:0] mem [DEPTH];
    logic [DATA_WIDTH-1:0] rd_data_reg;
    
    // Memory access (disabled in sleep mode)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data_reg <= '0;
        end else if (!sleep_mode) begin
            if (wr_en)
                mem[addr] <= wr_data;
            rd_data_reg <= mem[addr];
        end
    end
    
    assign rd_data = sleep_mode ? '0 : rd_data_reg;

endmodule

// Memory with multiple power modes
module memory_multi_mode #(
    parameter DEPTH = 1024,
    parameter WIDTH = 32
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [1:0]           power_mode,  // 00=active, 01=idle, 10=sleep, 11=off
    input  logic                 wr_en,
    input  logic [$clog2(DEPTH)-1:0] addr,
    input  logic [WIDTH-1:0]     wr_data,
    output logic [WIDTH-1:0]     rd_data
);

    logic [WIDTH-1:0] mem [DEPTH];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data <= '0;
        end else begin
            case (power_mode)
                2'b00: begin  // Active - full speed
                    if (wr_en)
                        mem[addr] <= wr_data;
                    rd_data <= mem[addr];
                end
                2'b01: begin  // Idle - clock gated internally
                    rd_data <= mem[addr];
                end
                2'b10: begin  // Sleep - minimal power
                    rd_data <= '0;
                end
                2'b11: begin  // Off - no access
                    rd_data <= '0;
                end
            endcase
        end
    end

endmodule

// Partitioned memory with selective power-down
module memory_partitioned #(
    parameter NUM_BANKS = 4,
    parameter BANK_SIZE = 256,
    parameter WIDTH = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [NUM_BANKS-1:0]    bank_sleep,
    input  logic                    wr_en,
    input  logic [$clog2(NUM_BANKS*BANK_SIZE)-1:0] addr,
    input  logic [WIDTH-1:0]        wr_data,
    output logic [WIDTH-1:0]        rd_data
);

    logic [$clog2(NUM_BANKS)-1:0] bank_sel;
    logic [$clog2(BANK_SIZE)-1:0] bank_addr;
    
    assign bank_sel = addr[$clog2(NUM_BANKS*BANK_SIZE)-1:$clog2(BANK_SIZE)];
    assign bank_addr = addr[$clog2(BANK_SIZE)-1:0];
    
    logic [WIDTH-1:0] bank_mem [NUM_BANKS][BANK_SIZE];
    
    genvar i;
    generate
        for (i = 0; i < NUM_BANKS; i++) begin : gen_banks
            always_ff @(posedge clk) begin
                if (!bank_sleep[i]) begin
                    if (wr_en && (bank_sel == i))
                        bank_mem[i][bank_addr] <= wr_data;
                end
            end
        end
    endgenerate
    
    assign rd_data = bank_sleep[bank_sel] ? '0 : bank_mem[bank_sel][bank_addr];

endmodule
