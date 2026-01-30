

module ex3_1;
    int arr[string];

    initial begin
        // arr = new[5];

        arr["Alice"] = 25;
        arr["Bob"] = 30;
        arr["Charlie"] = 20;
        arr["Diana"] = 35;
        arr["Eve"] = 22;

        if (arr.exists("Eve")) 
            $display("\nEve is %0d years old\n", arr["Eve"]);
        else 
            $display("Eve not found in array");
        
        if (arr.exists("Aaron")) 
            $display("\nAaron is %0d years old\n", arr["Aaron"]);
        else 
            $display("\nAaron not found in array\n");
        foreach (arr[i])
            $display("%s is %0d years old", i, arr[i]);

        $display("\nThere are %0d people in the array\n", arr.num());
        $finish();
    end



endmodule

module ex3_2;
    bit [7:0] memory[bit [31:0]];

    bit [7:0] data;
    initial begin
        memory[32'h1000] = 8'hAA;
        memory[32'h5000] = 8'hBB;
        memory[32'h1000_0000] = 8'hCC;
        memory[32'h0100_0000] = 8'hDD;
        data = memory[32'h1000];
        $display("Address 0x1000: 0x%0h", data);
        $display("memory[0x5000]      = 0x%h", memory[32'h0000_5000]);
        $display("memory[0x1000_0000] = 0x%h", memory[32'h1000_0000]);
        $display("memory[0x0100_0000] = 0x%h", memory[32'h0100_0000]);
        $display("Actual entries stored: %0d", memory.num());
        $finish();

    end

endmodule

module ex3_3;
    int arr[string];
    
    string name;
    int status;

    initial begin

        arr["A"] = $urandom_range(10,0);
        arr["B"] = $urandom_range(20,0);
        arr["C"] = $urandom_range(30,0);
        arr["D"] = $urandom_range(40,0);
        arr["E"] = $urandom_range(50,0);
        arr["F"] = $urandom_range(60,0);

        status = arr.first(name);

        while (status) begin
            $display("%s: %0d", name, arr[name]);
            status = arr.next(name);
        end
    end
    initial begin
        int total = 0;
        int count = 0;
        string name;
        int average;

        arr.first(name);

        do begin
            total += arr[name];
            count++;
        end while (arr.next(name));

        average = total / count;

        $display("Average score: %0d", average);

    
        $finish();


    end

endmodule