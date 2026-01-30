

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

