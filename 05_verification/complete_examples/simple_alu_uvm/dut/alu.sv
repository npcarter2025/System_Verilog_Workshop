// ============================================================================
// alu.sv - Simple ALU Design Under Test
// ============================================================================

module alu #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             valid,
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic [2:0]       op,
    output logic [WIDTH-1:0] result,
    output logic             ready
);

    typedef enum logic [2:0] {
        ADD  = 3'b000,
        SUB  = 3'b001,
        AND  = 3'b010,
        OR   = 3'b011,
        XOR  = 3'b100,
        SLL  = 3'b101,
        SRL  = 3'b110,
        SRA  = 3'b111
    } alu_op_e;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result <= '0;
            ready <= 1'b0;
        end else if (valid) begin
            case (op)
                ADD: result <= a + b;
                SUB: result <= a - b;
                AND: result <= a & b;
                OR:  result <= a | b;
                XOR: result <= a ^ b;
                SLL: result <= a << b[2:0];
                SRL: result <= a >> b[2:0];
                SRA: result <= $signed(a) >>> b[2:0];
                default: result <= '0;
            endcase
            ready <= 1'b1;
        end else begin
            ready <= 1'b0;
        end
    end

endmodule
