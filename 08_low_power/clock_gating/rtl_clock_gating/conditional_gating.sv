// Conditional Clock Gating
// Gates clock based on complex logic conditions

module conditional_gating_example #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             mode,
    input  logic             threshold_met,
    input  logic             data_valid,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Complex enable condition
    logic enable;
    assign enable = data_valid && (mode ? threshold_met : 1'b1);
    
    // Register with conditional gating
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (enable)
            data_out <= data_in;
    end
    
    // Synthesis tool will insert ICG based on 'enable' signal

endmodule

// State-dependent clock gating
module state_dependent_gating (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [2:0] state,
    input  logic [31:0] data_in,
    output logic [31:0] reg1,
    output logic [31:0] reg2
);

    localparam IDLE = 3'b000;
    localparam PROC = 3'b001;
    localparam WAIT = 3'b010;
    
    // Gate reg1 only in PROC state
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reg1 <= '0;
        else if (state == PROC)
            reg1 <= data_in + 1;
    end
    
    // Gate reg2 only when not in WAIT
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reg2 <= '0;
        else if (state != WAIT)
            reg2 <= data_in * 2;
    end

endmodule

// Data-dependent clock gating
module data_dependent_gating #(
    parameter WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] accumulator
);

    // Only accumulate non-zero values
    logic enable;
    assign enable = (data_in != '0);
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            accumulator <= '0;
        else if (enable)
            accumulator <= accumulator + data_in;
    end

endmodule

// Multi-condition clock gating
module multi_condition_gating (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        cond1,
    input  logic        cond2,
    input  logic        cond3,
    input  logic [31:0] data_in,
    output logic [31:0] result
);

    // AND of multiple conditions
    logic gate_enable;
    assign gate_enable = cond1 && cond2 && cond3;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            result <= '0;
        else if (gate_enable)
            result <= data_in;
    end

endmodule
