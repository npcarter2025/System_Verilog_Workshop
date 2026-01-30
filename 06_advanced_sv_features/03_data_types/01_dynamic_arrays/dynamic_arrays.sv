

module ex1_1_basic_dyn_arr;

    int dyn_arr1[]; 
    int dyn_arr2[];


    initial begin

        dyn_arr1 = new[10];
        dyn_arr2 = new[10];

        for (int i = 0; i < 10; i++) 
            dyn_arr1[i] = i;

        foreach (dyn_arr2[i])
            dyn_arr2[i] = i;

        $display("Array 1 size: %0d", dyn_arr1.size());

        foreach (dyn_arr1[i])
            $display("dyn_arr1[%0d] = %0d", i, dyn_arr1[i]);
        
        dyn_arr1.delete();
        dyn_arr2.delete();

    end
    
endmodule

module ex1_2_arr;

    int arr[];

    initial begin
        arr = new[5];

        for (int i = 0; i < 5; i++)     
            arr[i] = (i+1) * 10;

        $display("\nBefore Resizing (size=%0d):", arr.size());
        foreach (arr[i])
            $display("arr[%0d] = %0d", i, arr[i]);
        
        arr = new[8](arr);

        arr[5] = 60;
        arr[6] = 70;
        arr[7] = 80;

        $display("\nAfter Resizing (size=%0d):", arr.size());
        foreach (arr[i])
            $display("arr[%0d] = %0d", i, arr[i]);
        

    end

endmodule


module ex1_3_arr;

    int SIZE = 20;

    bit [31:0] arr[];

    initial begin

        $display("\n\n Ex 1.3");
        arr = new[SIZE];

        foreach (arr[i])
            arr[i] = $urandom_range(50, 10);
        
        foreach (arr[i])
            $display("  arr[%0d] = %0d", i, arr[i]);


        $display("Total = %0d\n", sum());

        $display("Min = %0d\n", min());
    end

    function int sum();
        int total = 0;
        for (int i = 0; i < arr.size(); i++) 
            total += arr[i];

        return total;
    endfunction

    function int min();
        int mn = 32'h7FFF_FFFF;
        foreach (arr[i])
            mn = (arr[i] < mn) ? arr[i] : mn;
        return mn;
    endfunction

endmodule