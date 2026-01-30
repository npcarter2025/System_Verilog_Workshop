// ============================================================================
// soft_constraints.sv - Soft Constraints (Can be overridden)
// ============================================================================

module soft_constraints;
    
    class packet;
        rand bit [7:0] addr;
        rand bit [15:0] data;
        
        // Soft constraint - can be overridden inline
        constraint soft_addr_c {
            soft addr inside {[8'h00:8'h7F]};
        }
        
        // Hard constraint - cannot be overridden
        constraint hard_data_c {
            data != 0;
        }
    endclass
    
    initial begin
        packet pkt = new();
        
        $display("=== With Soft Constraint ===");
        repeat(5) begin
            assert(pkt.randomize());
            $display("addr=0x%0h data=0x%0h", pkt.addr, pkt.data);
        end
        
        $display("\n=== Overriding Soft Constraint ===");
        repeat(5) begin
            // Override soft constraint inline
            assert(pkt.randomize() with {addr > 8'h80;});
            $display("addr=0x%0h data=0x%0h", pkt.addr, pkt.data);
        end
    end
    
endmodule
