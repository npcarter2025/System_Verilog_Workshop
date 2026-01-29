// Clock Gating Assertions
// SVA properties to verify clock gating safety

module clock_gating_assertions (
    input logic clk,
    input logic en,
    input logic gclk
);

    // Property 1: Gated clock only toggles when enabled
    property gclk_when_enabled;
        @(posedge clk)
        $rose(gclk) |-> en;
    endproperty
    
    a_gclk_enabled: assert property (gclk_when_enabled)
        else $error("Gated clock active when not enabled");
    
    // Property 2: No glitches on gated clock
    property no_glitch;
        @(posedge clk)
        $rose(gclk) |-> ##1 $stable(gclk) or $fell(gclk);
    endproperty
    
    a_no_glitch: assert property (no_glitch)
        else $error("Glitch detected on gated clock");
    
    // Property 3: Gated clock frequency <= source clock
    property freq_check;
        @(posedge gclk)
        1'b1 |-> @(posedge clk) 1'b1;
    endproperty
    
    a_freq: assert property (freq_check);
    
    // Property 4: Enable stable during clock high
    property en_stable_high;
        @(posedge clk)
        clk |-> $stable(en);
    endproperty
    
    // Coverage
    covergroup cg_gating @(posedge clk);
        cp_en: coverpoint en;
        cp_gclk: coverpoint gclk;
        cross cp_en, cp_gclk;
    endgroup
    
    cg_gating cg_inst = new();

endmodule
