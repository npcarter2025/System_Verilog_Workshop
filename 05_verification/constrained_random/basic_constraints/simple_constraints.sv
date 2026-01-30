// ============================================================================
// simple_constraints.sv - Basic SystemVerilog Constraints
// ============================================================================

module simple_constraints;
    
    class packet;
        rand bit [7:0] addr;
        rand bit [15:0] data;
        rand bit [1:0] cmd;
        
        // Basic range constraint
        constraint addr_range_c {
            addr inside {[8'h10:8'h20]};
        }
        
        // Multiple possibilities
        constraint cmd_c {
            cmd inside {2'b00, 2'b01, 2'b10};  // Not 2'b11
        }
        
        // Relational constraint
        constraint data_c {
            data < 16'h1000;
            data > 16'h0010;
        }
        
        function void display();
            $display("addr=0x%0h data=0x%0h cmd=%0b", addr, data, cmd);
        endfunction
    endclass
    
    class even_packet;
        rand bit [7:0] value;
        
        // Even numbers only
        constraint even_c {
            value[0] == 0;
        }
    endclass
    
    class power_of_two;
        rand bit [7:0] value;
        
        // Must be power of 2
        constraint pow2_c {
            $countones(value) == 1;
            value != 0;
        }
    endclass
    
    initial begin
        packet pkt = new();
        even_packet even = new();
        power_of_two pow2 = new();
        
        $display("=== Simple Constraints ===");
        repeat(5) begin
            assert(pkt.randomize());
            pkt.display();
        end
        
        $display("\n=== Even Numbers ===");
        repeat(5) begin
            assert(even.randomize());
            $display("value=%0d", even.value);
        end
        
        $display("\n=== Powers of Two ===");
        repeat(5) begin
            assert(pow2.randomize());
            $display("value=%0d", pow2.value);
        end
    end
    
endmodule
