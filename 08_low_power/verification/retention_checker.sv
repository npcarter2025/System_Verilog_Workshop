// Retention Checker
// Verifies data retention during power-down

module retention_checker #(
    parameter WIDTH = 32
) (
    input logic             clk,
    input logic             rst_n,
    input logic             save,
    input logic             restore,
    input logic [WIDTH-1:0] data
);

    logic [WIDTH-1:0] saved_data;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            saved_data <= '0;
        else if (save)
            saved_data <= data;
    end
    
    property data_retained;
        @(posedge clk) disable iff (!rst_n)
        restore |-> (data == saved_data);
    endproperty
    
    a_retention: assert property (data_retained)
        else $error("Retention check failed");

endmodule
