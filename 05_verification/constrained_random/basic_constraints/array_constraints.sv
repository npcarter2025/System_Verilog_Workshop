// ============================================================================
// array_constraints.sv - Array Constraints
// ============================================================================

module array_constraints;
    
    class array_packet;
        rand bit [7:0] data[];
        rand int length;
        
        // Array size constraint
        constraint length_c {
            length inside {[4:16]};
            data.size() == length;
        }
        
        // All elements must be non-zero
        constraint data_nonzero_c {
            foreach(data[i])
                data[i] != 0;
        }
        
        // Ascending order
        constraint ascending_c {
            foreach(data[i])
                if (i > 0)
                    data[i] > data[i-1];
        }
    endclass
    
    class unique_array;
        rand bit [7:0] values[10];
        
        // All values must be unique
        constraint unique_c {
            foreach(values[i])
                foreach(values[j])
                    if (i != j)
                        values[i] != values[j];
        }
    endclass
    
    class sum_array;
        rand bit [7:0] data[5];
        
        // Sum must equal 100
        constraint sum_c {
            data.sum() with (int'(item)) == 100;
        }
    endclass
    
    initial begin
        array_packet apkt = new();
        unique_array upkt = new();
        sum_array spkt = new();
        
        $display("=== Ascending Array ===");
        repeat(3) begin
            assert(apkt.randomize());
            $write("data = [");
            foreach(apkt.data[i])
                $write("%0d ", apkt.data[i]);
            $display("]");
        end
        
        $display("\n=== Unique Array ===");
        repeat(3) begin
            assert(upkt.randomize());
            $write("values = [");
            foreach(upkt.values[i])
                $write("%0d ", upkt.values[i]);
            $display("]");
        end
        
        $display("\n=== Sum Array (sum=100) ===");
        repeat(3) begin
            assert(spkt.randomize());
            int sum = 0;
            $write("data = [");
            foreach(spkt.data[i]) begin
                $write("%0d ", spkt.data[i]);
                sum += spkt.data[i];
            end
            $display("] sum=%0d", sum);
        end
    end
    
endmodule
