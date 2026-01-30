// ============================================================================
// mailbox_example.sv - Mailbox Communication in SystemVerilog
// ============================================================================
// Demonstrates inter-process communication using mailboxes
// ============================================================================

// ============================================================================
// Transaction Class
// ============================================================================
class packet;
    rand bit [7:0] data;
    rand bit [15:0] addr;
    int packet_id;
    static int next_id = 0;
    time timestamp;
    
    function new();
        packet_id = next_id++;
        timestamp = $time;
    endfunction
    
    function void display(string prefix = "");
        $display("%s [%0t] Packet#%0d: addr=0x%04h data=0x%02h", 
                prefix, timestamp, packet_id, addr, data);
    endfunction
endclass

// ============================================================================
// Generator (Produces Packets)
// ============================================================================
class generator;
    mailbox #(packet) gen2drv;  // Typed mailbox
    int num_packets;
    
    function new(mailbox #(packet) mbx);
        gen2drv = mbx;
        num_packets = 0;
    endfunction
    
    task run(int count);
        packet pkt;
        
        $display("[GENERATOR] Starting, generating %0d packets", count);
        
        repeat(count) begin
            pkt = new();
            assert(pkt.randomize());
            
            // Put into mailbox (blocking if full)
            gen2drv.put(pkt);
            num_packets++;
            
            pkt.display("[GEN→DRV]");
            #10;  // Simulate generation time
        end
        
        $display("[GENERATOR] Completed %0d packets", num_packets);
    endtask
endclass

// ============================================================================
// Driver (Consumes Packets and Drives)
// ============================================================================
class driver;
    mailbox #(packet) gen2drv;
    int num_packets;
    
    function new(mailbox #(packet) mbx);
        gen2drv = mbx;
        num_packets = 0;
    endfunction
    
    task run();
        packet pkt;
        
        $display("[DRIVER] Starting...");
        
        forever begin
            // Get from mailbox (blocking if empty)
            gen2drv.get(pkt);
            num_packets++;
            
            pkt.display("[DRV] Processing");
            drive_packet(pkt);
        end
    endtask
    
    task drive_packet(packet pkt);
        // Simulate driving
        #5;
        $display("[DRV] Drove packet #%0d", pkt.packet_id);
    endtask
endclass

// ============================================================================
// Monitor (Observes and Sends to Scoreboard)
// ============================================================================
class monitor;
    mailbox #(packet) mon2scb;
    int num_packets;
    
    function new(mailbox #(packet) mbx);
        mon2scb = mbx;
        num_packets = 0;
    endfunction
    
    task run();
        packet pkt;
        
        $display("[MONITOR] Starting...");
        
        forever begin
            // Simulate monitoring
            #15;
            
            pkt = new();
            assert(pkt.randomize());
            
            // Send to scoreboard
            mon2scb.put(pkt);
            num_packets++;
            
            pkt.display("[MON→SCB]");
        end
    endtask
endclass

// ============================================================================
// Scoreboard (Receives from Monitor)
// ============================================================================
class scoreboard;
    mailbox #(packet) mon2scb;
    int num_packets;
    
    function new(mailbox #(packet) mbx);
        mon2scb = mbx;
        num_packets = 0;
    endfunction
    
    task run();
        packet pkt;
        
        $display("[SCOREBOARD] Starting...");
        
        forever begin
            mon2scb.get(pkt);
            num_packets++;
            
            pkt.display("[SCB] Checking");
            check_packet(pkt);
        end
    endtask
    
    task check_packet(packet pkt);
        // Simulate checking
        #2;
        $display("[SCB] Packet #%0d checked OK", pkt.packet_id);
    endtask
endclass

// ============================================================================
// Bounded Mailbox Example
// ============================================================================
class bounded_mailbox_example;
    mailbox #(packet) bounded_mbx;
    
    function new();
        bounded_mbx = new(4);  // Max 4 items
    endfunction
    
    task producer();
        packet pkt;
        
        $display("[PRODUCER] Starting with bounded mailbox (max=4)");
        
        for (int i = 0; i < 10; i++) begin
            pkt = new();
            pkt.data = i;
            
            $display("[PRODUCER] Putting packet %0d (mailbox size before=%0d)", 
                    i, bounded_mbx.num());
            
            bounded_mbx.put(pkt);  // Will block if full
            
            $display("[PRODUCER] Put packet %0d (mailbox size after=%0d)", 
                    i, bounded_mbx.num());
            
            #5;
        end
    endtask
    
    task consumer();
        packet pkt;
        
        $display("[CONSUMER] Starting...");
        
        repeat(10) begin
            #20;  // Slow consumer
            
            $display("[CONSUMER] Getting packet (mailbox size before=%0d)", 
                    bounded_mbx.num());
            
            bounded_mbx.get(pkt);
            
            $display("[CONSUMER] Got packet %0d (mailbox size after=%0d)", 
                    pkt.packet_id, bounded_mbx.num());
        end
    endtask
    
    task run();
        fork
            producer();
            consumer();
        join
    endtask
endclass

// ============================================================================
// Try Methods (Non-Blocking)
// ============================================================================
class try_methods_example;
    mailbox #(packet) mbx;
    
    function new();
        mbx = new(2);  // Small mailbox
    endfunction
    
    task run();
        packet pkt;
        bit success;
        
        $display("\n=== Try Methods Example ===");
        
        // try_put (non-blocking put)
        for (int i = 0; i < 5; i++) begin
            pkt = new();
            pkt.data = i;
            
            success = mbx.try_put(pkt);
            
            if (success) begin
                $display("Successfully put packet %0d (size=%0d)", i, mbx.num());
            end else begin
                $display("Failed to put packet %0d - mailbox full (size=%0d)", 
                        i, mbx.num());
            end
        end
        
        // try_get (non-blocking get)
        for (int i = 0; i < 5; i++) begin
            success = mbx.try_get(pkt);
            
            if (success) begin
                $display("Successfully got packet (size=%0d)", mbx.num());
            end else begin
                $display("Failed to get packet - mailbox empty (size=%0d)", 
                        mbx.num());
            end
        end
    endtask
endclass

// ============================================================================
// Peek Method Example
// ============================================================================
class peek_example;
    mailbox #(packet) mbx;
    
    function new();
        mbx = new();
    endfunction
    
    task run();
        packet pkt, peeked_pkt;
        bit success;
        
        $display("\n=== Peek Example ===");
        
        // Put some packets
        for (int i = 0; i < 3; i++) begin
            pkt = new();
            pkt.data = i * 10;
            mbx.put(pkt);
        end
        
        $display("Mailbox size: %0d", mbx.num());
        
        // Peek (doesn't remove)
        success = mbx.try_peek(peeked_pkt);
        $display("Peeked: data=0x%02h (size still %0d)", 
                peeked_pkt.data, mbx.num());
        
        // Peek again
        success = mbx.try_peek(peeked_pkt);
        $display("Peeked again: data=0x%02h (size still %0d)", 
                peeked_pkt.data, mbx.num());
        
        // Now get (removes)
        mbx.get(pkt);
        $display("Got: data=0x%02h (size now %0d)", pkt.data, mbx.num());
        
        // Peek next item
        success = mbx.try_peek(peeked_pkt);
        $display("Peeked next: data=0x%02h (size still %0d)", 
                peeked_pkt.data, mbx.num());
    endtask
endclass

// ============================================================================
// Multiple Producers/Consumers
// ============================================================================
class multi_producer_consumer;
    mailbox #(packet) shared_mbx;
    
    function new();
        shared_mbx = new(10);
    endfunction
    
    task producer(int id, int count);
        packet pkt;
        
        $display("[PRODUCER_%0d] Starting", id);
        
        repeat(count) begin
            pkt = new();
            pkt.data = id * 100 + $urandom_range(0, 99);
            
            shared_mbx.put(pkt);
            $display("[PRODUCER_%0d] Put packet: data=0x%02h", id, pkt.data);
            
            #($urandom_range(5, 15));
        end
        
        $display("[PRODUCER_%0d] Done", id);
    endtask
    
    task consumer(int id, int count);
        packet pkt;
        
        $display("[CONSUMER_%0d] Starting", id);
        
        repeat(count) begin
            shared_mbx.get(pkt);
            $display("[CONSUMER_%0d] Got packet: data=0x%02h", id, pkt.data);
            
            #($urandom_range(10, 20));
        end
        
        $display("[CONSUMER_%0d] Done", id);
    endtask
    
    task run();
        fork
            producer(0, 10);
            producer(1, 10);
            consumer(0, 10);
            consumer(1, 10);
        join
    endtask
endclass

// ============================================================================
// Main Testbench
// ============================================================================
module mailbox_example;
    
    initial begin
        mailbox #(packet) gen2drv_mbx;
        mailbox #(packet) mon2scb_mbx;
        
        generator gen;
        driver drv;
        monitor mon;
        scoreboard scb;
        
        bounded_mailbox_example bounded;
        try_methods_example try_ex;
        peek_example peek_ex;
        multi_producer_consumer multi;
        
        $display("\n========================================");
        $display("   MAILBOX EXAMPLES");
        $display("========================================\n");
        
        // Test 1: Basic Generator-Driver-Monitor-Scoreboard
        $display("=== Test 1: Basic Mailbox Communication ===");
        
        gen2drv_mbx = new();  // Unbounded
        mon2scb_mbx = new();
        
        gen = new(gen2drv_mbx);
        drv = new(gen2drv_mbx);
        mon = new(mon2scb_mbx);
        scb = new(mon2scb_mbx);
        
        fork
            gen.run(10);
            drv.run();
            mon.run();
            scb.run();
        join_none
        
        #500;
        $display("Gen: %0d, Drv: %0d, Mon: %0d, Scb: %0d packets", 
                gen.num_packets, drv.num_packets, 
                mon.num_packets, scb.num_packets);
        
        // Test 2: Bounded Mailbox
        $display("\n=== Test 2: Bounded Mailbox ===");
        bounded = new();
        bounded.run();
        
        // Test 3: Try Methods
        try_ex = new();
        try_ex.run();
        
        // Test 4: Peek
        peek_ex = new();
        peek_ex.run();
        
        // Test 5: Multiple Producers/Consumers
        $display("\n=== Test 5: Multiple Producers/Consumers ===");
        multi = new();
        multi.run();
        
        #1000;
        $display("\n========================================");
        $display("   ALL TESTS COMPLETE");
        $display("========================================\n");
        $finish;
    end
    
endmodule

/*
 * MAILBOX IN SYSTEMVERILOG:
 * 
 * CONCEPT:
 * - Inter-process communication mechanism
 * - FIFO queue for passing objects
 * - Producer-consumer pattern
 * - Thread-safe
 * 
 * DECLARATION:
 * mailbox mbx;              // Untyped
 * mailbox #(type) mbx;      // Typed (recommended)
 * 
 * CREATION:
 * mbx = new();              // Unbounded
 * mbx = new(size);          // Bounded (max size)
 * 
 * METHODS:
 * 
 * Blocking:
 * - put(data):     Put item (blocks if full)
 * - get(data):     Get item (blocks if empty)
 * - peek(data):    Look at first item (doesn't remove)
 * 
 * Non-Blocking:
 * - try_put(data):  Returns 1 if success, 0 if full
 * - try_get(data):  Returns 1 if success, 0 if empty
 * - try_peek(data): Returns 1 if success, 0 if empty
 * 
 * Query:
 * - num():         Number of items in mailbox
 * 
 * BOUNDED vs UNBOUNDED:
 * 
 * Unbounded:
 * + Never blocks on put
 * + Simple to use
 * - Can grow indefinitely
 * - Memory issues
 * 
 * Bounded:
 * + Controlled memory
 * + Back-pressure mechanism
 * - Can block producer
 * - Need to size correctly
 * 
 * USE CASES:
 * 1. Generator → Driver
 * 2. Monitor → Scoreboard
 * 3. Agent → Agent
 * 4. Stimulus → Checker
 * 5. Producer → Consumer
 * 
 * ADVANTAGES:
 * + Thread-safe
 * + Simple API
 * + Blocking/non-blocking
 * + Typed safety
 * + FIFO ordering
 * 
 * DISADVANTAGES:
 * - FIFO only (no priority)
 * - No broadcast
 * - No filtering
 * - Blocking can deadlock
 * 
 * BEST PRACTICES:
 * 1. Use typed mailboxes
 * 2. Bound size if memory limited
 * 3. Use try_* for non-blocking
 * 4. Check num() before operations
 * 5. Handle blocking gracefully
 * 
 * COMMON PATTERNS:
 * 
 * 1. Generator-Driver:
 * mailbox #(transaction) gen2drv = new();
 * generator gen = new(gen2drv);
 * driver drv = new(gen2drv);
 * 
 * 2. Monitor-Scoreboard:
 * mailbox #(transaction) mon2scb = new();
 * monitor mon = new(mon2scb);
 * scoreboard scb = new(mon2scb);
 * 
 * 3. Pipelined:
 * gen → [mbx1] → stage1 → [mbx2] → stage2
 * 
 * BLOCKING BEHAVIOR:
 * 
 * put() on full bounded mailbox:
 * - Blocks until space available
 * - Other processes can run
 * - Resumes when get() called
 * 
 * get() on empty mailbox:
 * - Blocks until data available
 * - Other processes can run
 * - Resumes when put() called
 * 
 * DEADLOCK AVOIDANCE:
 * ✓ Use try_* methods
 * ✓ Timeout mechanisms
 * ✓ Size mailboxes appropriately
 * ✓ Don't create circular waits
 * ✓ Producer/consumer in different threads
 * 
 * DEBUGGING:
 * - Print num() regularly
 * - Log put/get operations
 * - Check for blocking
 * - Monitor growth
 * - Timeout detection
 * 
 * ALTERNATIVES:
 * - Events (synchronization only)
 * - Semaphores (counting)
 * - Channels (deprecated)
 * - Queues (not thread-safe)
 * 
 * TYPED vs UNTYPED:
 * 
 * Typed:
 * + Compile-time checking
 * + No casting needed
 * + Safer
 * + Recommended
 * 
 * Untyped:
 * + Flexible
 * - Runtime errors
 * - Need casting
 * - Not recommended
 * 
 * PERFORMANCE:
 * - Lightweight
 * - Fast operations
 * - Minimal overhead
 * - Good for high throughput
 * 
 * TYPICAL SIZE:
 * - Small: 1-10 (tight coupling)
 * - Medium: 10-100 (normal)
 * - Large: 100+ (burst handling)
 * - Unbounded: Development/debug
 * 
 * WHEN TO USE:
 * ✓ Producer-consumer pattern
 * ✓ Inter-component communication
 * ✓ Stimulus generation
 * ✓ Response collection
 * ✓ Pipelined operations
 * 
 * WHEN NOT TO USE:
 * ✗ Simple synchronization (use events)
 * ✗ Resource locking (use semaphores)
 * ✗ Broadcast (use events)
 * ✗ Priority queue (use custom class)
 */
