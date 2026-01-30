// ============================================================================
// dist_constraints.sv - Distribution Constraints
// ============================================================================

module dist_constraints;
    
    class weighted_packet;
        rand bit [1:0] priority;
        rand bit [7:0] data;
        
        // Distribution: := means weighted distribution
        constraint priority_dist_c {
            priority dist {
                2'b00 := 50,  // 50% weight
                2'b01 := 30,  // 30% weight
                2'b10 := 15,  // 15% weight
                2'b11 := 5    // 5% weight
            };
        }
        
        // Range distribution: :/ means equal weight across range
        constraint data_dist_c {
            data dist {
                [0:63] := 70,      // 70% weight for 0-63
                [64:127] := 20,    // 20% weight for 64-127
                [128:255] := 10    // 10% weight for 128-255
            };
        }
    endclass
    
    class traffic_mix;
        rand bit [1:0] pkt_type;
        
        // Traffic mix: 60% reads, 30% writes, 10% other
        constraint traffic_c {
            pkt_type dist {
                2'b00 := 60,  // READ
                2'b01 := 30,  // WRITE
                [2'b10:2'b11] :/ 10  // OTHER (split equally)
            };
        }
    endclass
    
    initial begin
        weighted_packet wpkt = new();
        traffic_mix tmix = new();
        int priority_count[4];
        int traffic_count[4];
        
        // Test weighted distribution
        $display("=== Priority Distribution (1000 samples) ===");
        repeat(1000) begin
            assert(wpkt.randomize());
            priority_count[wpkt.priority]++;
        end
        
        foreach(priority_count[i])
            $display("Priority %0d: %0d times (%0.1f%%)", 
                    i, priority_count[i], (priority_count[i]/10.0));
        
        // Test traffic mix
        $display("\n=== Traffic Mix (1000 samples) ===");
        repeat(1000) begin
            assert(tmix.randomize());
            traffic_count[tmix.pkt_type]++;
        end
        
        $display("READ (00): %0d times (%0.1f%%)", 
                traffic_count[0], (traffic_count[0]/10.0));
        $display("WRITE (01): %0d times (%0.1f%%)", 
                traffic_count[1], (traffic_count[1]/10.0));
        $display("OTHER (10/11): %0d times (%0.1f%%)", 
                traffic_count[2]+traffic_count[3], 
                ((traffic_count[2]+traffic_count[3])/10.0));
    end
    
endmodule
