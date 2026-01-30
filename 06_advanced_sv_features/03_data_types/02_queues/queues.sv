

module queue_ex_2_1;

    int q[$];

    initial begin

        for (int i = 0; i < 5; i++) 
            q.push_back(i);

        q.push_front(-1);
        q.push_front(-2);

        foreach(q[i])
            $display("q[%0d] = %0d", i, q[i]);
        
        q.pop_back();
        q.pop_front();
        $display("\n");
        foreach(q[i])
            $display("q[%0d] = %0d", i, q[i]);
        $display("End of ex2.1 \n");
    end
endmodule

module queue_ex_2_4;
    int q[$:8];

    initial begin

        for (int i = 0; i < 10; i++) begin
            
            if (q.size() < 8) begin
                q.push_back(i);

                $display("q[%0d] = %0d", i, q[i]);
            end else begin
                $display("Queue was full");
            end
        end
    end

endmodule

module queue_ex_2_5;

    int q[$:20];

    initial begin

        for (int i = 0; i < 20; i++) begin

            q.push_back(i);
        end
        for (int i = 0; i < 5; i++)
            q.insert(5, 12345);

        foreach (q[i])
            $display("q[%0d] = %0d", i, q[i]);

    end

endmodule

function void insert(q[$]);

endfunction

module priority_queue;

    typedef struct packed {
        int prio;
        int data;
    } pq_item_t;


    pq_item_t pq[$];


    function void insert_priority(int pri, int d);
        pq_item_t new_item;

        new_item.prio = pri;
        new_item.data = d;

        if (pq.size() == 0) begin
            pq.push_back(new_item);
            return;
        end


        for (int i = 0; i < pq.size(); i++) begin
            if (new_item.prio > pq[i].prio) begin 
                pq.insert(i, new_item);
                return;
            end
        end

        pq.push_back(new_item);

    endfunction

    initial begin
        insert_priority(5, 100);   // Medium priority
        insert_priority(10, 200);  // High priority (should go to front)
        insert_priority(3, 300);   // Low priority (should go to back)
        insert_priority(7, 400);   // Should slot in between

        foreach (pq[i])
            $display("Processing: priority=%0d, data=%0d", pq[i].prio, pq[i].data);

    end


endmodule

