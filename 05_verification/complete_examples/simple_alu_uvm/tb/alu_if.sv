// ============================================================================
// alu_if.sv - ALU Interface
// ============================================================================

interface alu_if #(parameter WIDTH = 8)(input logic clk);
    logic rst_n;
    logic valid;
    logic [WIDTH-1:0] a;
    logic [WIDTH-1:0] b;
    logic [2:0] op;
    logic [WIDTH-1:0] result;
    logic ready;
    
    clocking driver_cb @(posedge clk);
        output valid, a, b, op;
        input result, ready;
    endclocking
    
    clocking monitor_cb @(posedge clk);
        input valid, a, b, op, result, ready;
    endclocking
    
    modport driver(clocking driver_cb, output rst_n);
    modport monitor(clocking monitor_cb, input rst_n);
    modport dut(input clk, rst_n, valid, a, b, op, output result, ready);
    
endinterface
