// Pipeline Clock Gating
// Gates entire pipeline stages when not in use

module gated_pipeline #(
    parameter WIDTH = 32,
    parameter STAGES = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             pipeline_en,  // Enable entire pipeline
    input  logic [WIDTH-1:0] data_in,
    input  logic             valid_in,
    output logic [WIDTH-1:0] data_out,
    output logic             valid_out
);

    // Pipeline stages
    logic [WIDTH-1:0] stage [STAGES];
    logic [STAGES-1:0] valid;
    
    // Individual stage enables
    logic [STAGES-1:0] stage_en;
    
    // Generate enable for each stage
    always_comb begin
        stage_en[0] = valid_in && pipeline_en;
        for (int i = 1; i < STAGES; i++)
            stage_en[i] = valid[i-1] && pipeline_en;
    end
    
    // Pipeline with clock gating per stage
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < STAGES; i++) begin
                stage[i] <= '0;
                valid[i] <= 0;
            end
        end else begin
            // Stage 0
            if (stage_en[0]) begin
                stage[0] <= data_in + 1;
                valid[0] <= 1;
            end else begin
                valid[0] <= 0;
            end
            
            // Other stages
            for (int i = 1; i < STAGES; i++) begin
                if (stage_en[i]) begin
                    stage[i] <= stage[i-1] + 1;
                    valid[i] <= 1;
                end else begin
                    valid[i] <= 0;
                end
            end
        end
    end
    
    assign data_out = stage[STAGES-1];
    assign valid_out = valid[STAGES-1];

endmodule
