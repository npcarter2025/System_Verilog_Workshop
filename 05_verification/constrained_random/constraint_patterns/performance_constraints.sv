// ============================================================================
// performance_constraints.sv - Performance-Oriented Constraint Patterns
// ============================================================================

module performance_constraints;
    
    // ========================================================================
    // Bandwidth Control
    // ========================================================================
    
    class bandwidth_controlled_traffic;
        rand bit [31:0] data[];
        rand int delay_cycles;
        rand bit [15:0] burst_size;
        
        real target_bandwidth;  // MB/s
        int clock_freq_mhz;     // MHz
        
        function new(real bw = 100.0, int freq = 100);
            target_bandwidth = bw;
            clock_freq_mhz = freq;
        endfunction
        
        // Control burst size based on bandwidth
        constraint burst_size_c {
            burst_size inside {[4:256]};
            data.size() == burst_size;
        }
        
        // Delay to achieve target bandwidth
        constraint delay_c {
            delay_cycles inside {[1:100]};
            
            // Approximate: larger bursts, less frequent
            (burst_size < 16)  -> (delay_cycles inside {[1:10]});
            (burst_size < 64)  -> (delay_cycles inside {[5:20]});
            (burst_size >= 64) -> (delay_cycles inside {[10:50]});
        }
    endclass
    
    // ========================================================================
    // Queue Depth Management
    // ========================================================================
    
    class queue_aware_traffic;
        rand bit [7:0] outstanding_requests;
        rand bit [3:0] new_requests;
        int max_queue_depth;
        
        function new(int max_depth = 32);
            max_queue_depth = max_depth;
        endfunction
        
        // Don't overflow queue
        constraint queue_c {
            outstanding_requests + new_requests <= max_queue_depth;
        }
        
        // Distributed traffic generation
        constraint new_req_c {
            new_requests dist {
                0      := 10,  // Idle
                [1:2]  := 50,  // Light
                [3:4]  := 30,  // Medium
                [5:8]  := 10   // Heavy
            };
        }
        
        // Back off when queue is full
        constraint backoff_c {
            (outstanding_requests > (max_queue_depth * 3 / 4)) -> {
                new_requests inside {[0:2]};
            }
        }
    endclass
    
    // ========================================================================
    // Cache-Aware Access Patterns
    // ========================================================================
    
    class cache_friendly_access;
        rand bit [31:0] addr;
        rand bit [5:0] cache_line_offset;
        rand bit hit_rate_mode;  // 0=low hit, 1=high hit
        
        int cache_line_size = 64;
        int cache_size = 32768;  // 32KB
        
        // High locality for cache hits
        constraint locality_c {
            hit_rate_mode -> {
                // Stay within small address range
                addr inside {[32'h1000:32'h1FFF]};
                
                // Sequential within cache line
                cache_line_offset inside {[0:15]};
            }
        }
        
        // Random pattern for cache misses
        constraint random_c {
            !hit_rate_mode -> {
                // Spread across large range
                addr inside {[32'h0:32'hFFFF_FFFF]};
            }
        }
        
        // Cache line aligned base
        constraint align_c {
            addr[5:0] == cache_line_offset;
        }
    endclass
    
    // ========================================================================
    // Latency-Sensitive Traffic
    // ========================================================================
    
    class latency_sensitive_packet;
        rand bit [1:0] priority;
        rand bit [15:0] size;
        rand int max_latency;  // Target latency in cycles
        
        typedef enum bit [1:0] {
            REALTIME = 2'b11,
            HIGH     = 2'b10,
            MEDIUM   = 2'b01,
            LOW      = 2'b00
        } priority_e;
        
        // Small packets for low latency
        constraint size_latency_c {
            (priority == REALTIME) -> {
                size inside {[64:256]};
                max_latency inside {[10:50]};
            }
            
            (priority == HIGH) -> {
                size inside {[256:1024]};
                max_latency inside {[50:200]};
            }
            
            (priority == MEDIUM) -> {
                size inside {[1024:4096]};
                max_latency inside {[200:1000]};
            }
            
            (priority == LOW) -> {
                size inside {[4096:65536]};
                max_latency inside {[1000:10000]};
            }
        }
    endclass
    
    // ========================================================================
    // Throughput Optimization
    // ========================================================================
    
    class throughput_optimized_burst;
        rand bit [7:0] burst_length;
        rand bit [2:0] burst_size;
        rand bit      back_to_back;
        
        // Longer bursts for better throughput
        constraint burst_c {
            burst_length inside {[8:256]};
            burst_size inside {2, 3};  // 4 or 8 bytes per beat
        }
        
        // Back-to-back for maximum throughput
        constraint b2b_c {
            back_to_back dist {1 := 80, 0 := 20};
        }
        
        // Power-of-2 bursts for efficiency
        constraint pow2_c {
            $countones(burst_length) == 1;
        }
    endclass
    
    // ========================================================================
    // Mixed Traffic Patterns
    // ========================================================================
    
    class mixed_traffic_generator;
        rand bit [1:0] traffic_type;
        rand bit [31:0] addr;
        rand bit [15:0] size;
        rand int spacing;
        
        typedef enum bit [1:0] {
            STREAMING = 2'b00,  // Sequential, large bursts
            RANDOM    = 2'b01,  // Random access, small bursts
            LATENCY   = 2'b10,  // Small, time-critical
            BULK      = 2'b11   // Large transfers
        } traffic_e;
        
        // Traffic mix (realistic distribution)
        constraint traffic_mix_c {
            traffic_type dist {
                STREAMING := 40,
                RANDOM    := 30,
                LATENCY   := 20,
                BULK      := 10
            };
        }
        
        // Type-specific constraints
        constraint type_specific_c {
            (traffic_type == STREAMING) -> {
                size inside {[256:1024]};
                spacing inside {[1:5]};
                // Sequential addresses
                addr[11:0] inside {[0:4095]};  // Stay in 4KB page
            }
            
            (traffic_type == RANDOM) -> {
                size inside {[4:64]};
                spacing inside {[5:50]};
            }
            
            (traffic_type == LATENCY) -> {
                size inside {[4:16]};
                spacing inside {[1:3]};
            }
            
            (traffic_type == BULK) -> {
                size inside {[4096:65536]};
                spacing inside {[10:100]};
            }
        }
    endclass
    
    // ========================================================================
    // Power-Aware Traffic
    // ========================================================================
    
    class power_aware_traffic;
        rand bit [7:0] activity_level;  // 0-100%
        rand bit [15:0] burst_size;
        rand int idle_cycles;
        rand bit      power_save_mode;
        
        // Activity level determines aggressiveness
        constraint activity_c {
            activity_level inside {[10:90]};
        }
        
        // Lower activity = longer idle
        constraint idle_c {
            (activity_level < 30) -> (idle_cycles inside {[100:1000]});
            (activity_level < 60) -> (idle_cycles inside {[10:100]});
            (activity_level >= 60) -> (idle_cycles inside {[1:10]});
        }
        
        // Power save mode: smaller bursts, longer idle
        constraint power_save_c {
            power_save_mode -> {
                burst_size inside {[1:16]};
                idle_cycles inside {[50:500]};
            }
        }
        
        constraint normal_c {
            !power_save_mode -> {
                burst_size inside {[16:256]};
                idle_cycles inside {[1:50]};
            }
        }
    endclass
    
    // ========================================================================
    // Stress Test Pattern
    // ========================================================================
    
    class stress_test_pattern;
        rand bit [7:0] concurrent_streams;
        rand bit [15:0] transfer_size;
        rand bit       max_bandwidth_mode;
        
        // Multiple concurrent streams
        constraint streams_c {
            concurrent_streams inside {[1:16]};
        }
        
        // Stress mode: maximize everything
        constraint stress_c {
            max_bandwidth_mode -> {
                concurrent_streams >= 8;
                transfer_size inside {[1024:65536]};
            }
        }
        
        constraint normal_c {
            !max_bandwidth_mode -> {
                concurrent_streams inside {[1:4]};
                transfer_size inside {[64:4096]};
            }
        }
    endclass
    
    initial begin
        bandwidth_controlled_traffic bw_traffic;
        queue_aware_traffic queue_traffic;
        cache_friendly_access cache_access;
        latency_sensitive_packet lat_pkt;
        throughput_optimized_burst tp_burst;
        mixed_traffic_generator mixed;
        power_aware_traffic power;
        stress_test_pattern stress;
        
        $display("=== Performance Constraint Patterns ===\n");
        
        // Bandwidth control
        $display("--- Bandwidth Controlled Traffic (100 MB/s) ---");
        bw_traffic = new(100.0, 100);
        repeat(5) begin
            assert(bw_traffic.randomize());
            $display("burst=%0d bytes, delay=%0d cycles",
                    bw_traffic.burst_size * 4, bw_traffic.delay_cycles);
        end
        
        // Queue management
        $display("\n--- Queue Aware Traffic (max=32) ---");
        queue_traffic = new(32);
        queue_traffic.outstanding_requests = 20;
        repeat(5) begin
            assert(queue_traffic.randomize());
            $display("outstanding=%0d, new=%0d, total=%0d",
                    queue_traffic.outstanding_requests,
                    queue_traffic.new_requests,
                    queue_traffic.outstanding_requests + queue_traffic.new_requests);
        end
        
        // Cache-friendly
        $display("\n--- Cache-Friendly Access ---");
        cache_access = new();
        $display("High hit rate mode:");
        cache_access.hit_rate_mode = 1;
        repeat(3) begin
            assert(cache_access.randomize());
            $display("  addr=0x%08h", cache_access.addr);
        end
        $display("Low hit rate mode:");
        cache_access.hit_rate_mode = 0;
        repeat(3) begin
            assert(cache_access.randomize());
            $display("  addr=0x%08h", cache_access.addr);
        end
        
        // Latency-sensitive
        $display("\n--- Latency-Sensitive Traffic ---");
        lat_pkt = new();
        repeat(5) begin
            assert(lat_pkt.randomize());
            $display("priority=%0d, size=%0d bytes, max_lat=%0d cycles",
                    lat_pkt.priority, lat_pkt.size, lat_pkt.max_latency);
        end
        
        // Throughput optimized
        $display("\n--- Throughput Optimized Bursts ---");
        tp_burst = new();
        repeat(5) begin
            assert(tp_burst.randomize());
            $display("length=%0d, size=%0dB, b2b=%0b",
                    tp_burst.burst_length, (1 << tp_burst.burst_size), 
                    tp_burst.back_to_back);
        end
        
        // Mixed traffic
        $display("\n--- Mixed Traffic Generator ---");
        mixed = new();
        repeat(10) begin
            assert(mixed.randomize());
            $display("type=%0d, size=%0d, spacing=%0d",
                    mixed.traffic_type, mixed.size, mixed.spacing);
        end
        
        // Power-aware
        $display("\n--- Power-Aware Traffic ---");
        power = new();
        repeat(5) begin
            assert(power.randomize());
            $display("activity=%0d%%, burst=%0d, idle=%0d, power_save=%0b",
                    power.activity_level, power.burst_size, 
                    power.idle_cycles, power.power_save_mode);
        end
        
        // Stress test
        $display("\n--- Stress Test Pattern ---");
        stress = new();
        stress.max_bandwidth_mode = 1;
        repeat(3) begin
            assert(stress.randomize());
            $display("streams=%0d, size=%0d",
                    stress.concurrent_streams, stress.transfer_size);
        end
    end
    
endmodule

/*
 * PERFORMANCE CONSTRAINT PATTERNS:
 * 
 * KEY METRICS:
 * 1. Bandwidth (MB/s, GB/s)
 * 2. Latency (cycles, ns)
 * 3. Throughput (transactions/sec)
 * 4. Queue depth / utilization
 * 5. Power consumption
 * 
 * PATTERNS:
 * - Bandwidth Control: Size + spacing relationships
 * - Queue Management: Outstanding vs new requests
 * - Cache Optimization: Locality of reference
 * - Latency Optimization: Small, frequent transfers
 * - Throughput Optimization: Large, back-to-back bursts
 * 
 * TESTING STRATEGIES:
 * 1. Vary traffic mix (streaming, random, latency-sensitive)
 * 2. Stress tests (max bandwidth, max queue depth)
 * 3. Power modes (active, idle, power-save)
 * 4. Realistic workloads (measured from real systems)
 * 
 * TRADE-OFFS:
 * - Latency vs Throughput
 * - Power vs Performance
 * - Fairness vs Efficiency
 * - Complexity vs Effectiveness
 */
