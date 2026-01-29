// Gated Compute Unit
// Power gates entire functional block when idle

module gated_compute_unit #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    input  logic [WIDTH-1:0] operand_a,
    input  logic [WIDTH-1:0] operand_b,
    input  logic [1:0]       operation,  // 00=add, 01=sub, 10=mul, 11=div
    output logic [WIDTH-1:0] result,
    output logic             valid
);

    // Power control
    logic power_gate_en;
    logic clk_gated;
    
    // Generate power gate enable with delay
    logic [3:0] enable_delay;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            enable_delay <= 4'b0000;
        else
            enable_delay <= {enable_delay[2:0], enable};
    end
    
    assign power_gate_en = |enable_delay;  // Keep powered for a few cycles
    
    // Clock gating
    icg_cell u_icg (
        .clk(clk),
        .en(power_gate_en),
        .test_en(1'b0),
        .gclk(clk_gated)
    );
    
    // Compute logic (only active when powered)
    logic [WIDTH-1:0] result_internal;
    
    always_ff @(posedge clk_gated or negedge rst_n) begin
        if (!rst_n) begin
            result_internal <= '0;
            valid <= 1'b0;
        end else if (enable) begin
            case (operation)
                2'b00: result_internal <= operand_a + operand_b;
                2'b01: result_internal <= operand_a - operand_b;
                2'b10: result_internal <= operand_a * operand_b[15:0];
                2'b11: result_internal <= operand_a / operand_b;
            endcase
            valid <= 1'b1;
        end else begin
            valid <= 1'b0;
        end
    end
    
    assign result = result_internal;

endmodule

// Complete power-gated block with isolation
module power_gated_block #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             power_en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Power control signals
    logic iso_en;
    logic save, restore;
    
    // Power control FSM
    typedef enum logic [1:0] {
        POWERED    = 2'b00,
        SAVING     = 2'b01,
        POWERED_OFF = 2'b10,
        RESTORING  = 2'b11
    } power_state_t;
    
    power_state_t state;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= POWERED;
        else begin
            case (state)
                POWERED: if (!power_en) state <= SAVING;
                SAVING: state <= POWERED_OFF;
                POWERED_OFF: if (power_en) state <= RESTORING;
                RESTORING: state <= POWERED;
            endcase
        end
    end
    
    assign save = (state == SAVING);
    assign restore = (state == RESTORING);
    assign iso_en = (state == POWERED_OFF);
    
    // Internal logic
    logic [WIDTH-1:0] data_internal;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_internal <= '0;
        else if (state == POWERED)
            data_internal <= data_in + 1;
    end
    
    // Isolation cell
    logic [WIDTH-1:0] data_isolated;
    assign data_isolated = iso_en ? '0 : data_internal;
    
    assign data_out = data_isolated;

endmodule
