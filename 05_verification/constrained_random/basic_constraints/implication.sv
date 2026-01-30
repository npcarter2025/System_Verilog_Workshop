// ============================================================================
// implication.sv - Implication Constraint (->)
// ============================================================================

module implication;
    
    class conditional_packet;
        rand bit write;
        rand bit [31:0] addr;
        rand bit [31:0] wdata;
        rand bit [3:0] strb;
        
        // If write, then strb must be valid
        constraint write_strb_c {
            write -> (strb != 4'b0000);
        }
        
        // If write to special range, use all strobes
        constraint special_range_c {
            (write && (addr inside {[32'h1000:32'h1FFF]})) -> (strb == 4'b1111);
        }
        
        // If read, wdata doesn't matter
        constraint read_wdata_c {
            !write -> (wdata == 0);
        }
    endclass
    
    class protocol_packet;
        rand bit [1:0] cmd;
        rand bit [7:0] length;
        rand bit burst;
        
        // If burst, length must be > 1
        constraint burst_length_c {
            burst -> (length > 1);
        }
        
        // Single transfers can't be bursts
        constraint single_c {
            (length == 1) -> (burst == 0);
        }
        
        // Certain commands require burst mode
        constraint cmd_burst_c {
            (cmd == 2'b11) -> (burst == 1);
        }
    endclass
    
    initial begin
        conditional_packet cpkt = new();
        protocol_packet ppkt = new();
        
        $display("=== Conditional Packet ===");
        repeat(10) begin
            assert(cpkt.randomize());
            $display("write=%0b addr=0x%0h wdata=0x%0h strb=%04b",
                    cpkt.write, cpkt.addr, cpkt.wdata, cpkt.strb);
        end
        
        $display("\n=== Protocol Packet ===");
        repeat(10) begin
            assert(ppkt.randomize());
            $display("cmd=%02b length=%0d burst=%0b",
                    ppkt.cmd, ppkt.length, ppkt.burst);
        end
    end
    
endmodule
