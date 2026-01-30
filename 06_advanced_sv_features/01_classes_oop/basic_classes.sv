

class BankAccount;
    // Properties
    int account_number;
    real balance;
    string owner_name;
    
    // Constructor
    function new(int acct_num, real bal, string name);
        account_number = acct_num;
        balance = bal;
        owner_name = name;
    endfunction

    function void display_info();
        string formatted_output;

        formatted_output = $sformatf("Account: %0d, Balance: $%0.2f, Owner: %0s", account_number, balance, owner_name);
        $display("%s", formatted_output);
    endfunction

endclass

module bank_tb;
    int acct = 12345;
    real bal = 1000.50;
    string name = "John Doe";

    initial begin
        BankAccount account = new(acct, bal, name);

        $display("\n\nacct: %0d, bal: $%0.2f, name: %s\n\n", account.account_number, account.balance, account.owner_name);

        account.display_info();
        $display("\n\n");
        $finish();
    end

endmodule

class Rectangle;
    int width;
    int height;

    function new(int w = 1, int h = 1);
        width = w;
        height = h;
    endfunction

    function int area();
        return (width * height);
    endfunction

    function int perimeter();
        return (2*(width+height));
    endfunction

    function bit is_square();
        return (width == height);
    endfunction

    function void scale(int factor);
        width *= factor;
        height *= factor;
    endfunction


    function int compare(Rectangle other);
        if (this.area() > other.area())
            return 1;
        else if (this.area() == other.area())
            return 0;
        else
            return -1;
    endfunction

    function void display_info();
        string formatted_output;
        formatted_output = $sformatf("Height = %0d, Width = %0d\n", height, width);
        $display("%s", formatted_output);
    endfunction

endclass

// function int rec_compare(Rectangle r1, Rectangle r2);

//     int a1 = r1.area();
//     int a2 = r2.area();

//     int res = (a1 > a2) ? 1 :
//             (a1 == a2) ? 0 : -1;
//     return res;
// endfunction



module Rectangle_tb;

    Rectangle r1;
    Rectangle r2;
    int a, a1, a2, a3, a4, a5;

    initial begin

        r1 = new();
        r2 = new(5, 3);
        a1 = r1.compare(r2);
        $display("\nBegin Rectangle_tb\n\n");
        $display("a1 = %0d\n", a1);
        r1.scale(50);
        a1 = r1.compare(r2);

        $display("a1 = %0d\n", a1);

        a = r2.area();
        r2.scale(2);
        r1.display_info();

        r2.display_info();

        $display("r1 area = %0d\n", r1.area());

        $display("r1 perimeter = %0d\n", r1.perimeter());

        $display("r2 is_square() = %0d\n", r2.is_square());
        $finish();
    end
endmodule

class vehicle;
    string brand;
    int year;
    int speed;

    function new(string brnd, int yr, int spd);
        brand = brnd;
        year = yr;
        speed = spd;
    endfunction

    virtual function void accelerate(int amount);
        speed += amount;
        $display("  Accelerated by %0d mph, new speed: %0d mph", amount, speed);
    endfunction

    virtual function void brake(int amount);
        speed -= amount;
        $display("  Braked by %0d mph, new speed: %0d mph", amount, speed);
    endfunction

    virtual function void display();
        string fmt_output;
        fmt_output = $sformatf("%s %0d, Speed: %0d mph", brand, year, speed);
        $write("%s", fmt_output);
    endfunction


endclass

class car extends vehicle;

    int num_doors;

    function new(string brnd, int yr, int spd, int doors);
        super.new(brnd, yr, spd);
        num_doors = doors;

    endfunction

    function void display();
        $write("Car: ");
        super.display();
        $write(", Doors: %0d\n", num_doors);
    endfunction

    function void honk();
        $display("Beep, beep!");
    endfunction

endclass

class motorcycle extends vehicle;
    bit has_sidecar;

    function new(string brnd, int yr, int spd, bit has_sdcar);
        super.new(brnd, yr, spd);
        has_sidecar = has_sdcar;
    endfunction

    function void display();
        $write("Motorcycle: ");
        super.display();
        $display(", Sidecar: %s", has_sidecar ? "Yes" : "No");
    endfunction

    function void wheelie();
        $display("Doing a wheelie");
    endfunction

endclass



module vehicle_tb;
    car c1;
    motorcycle m1;

    initial begin
        $display("\n=== Testing Vehicle Hierarchy ===\n");
        
        // Create car
        c1 = new("Toyota", 2020, 60, 4);
        c1.display();
        c1.honk();
        
        $display("");
        
        // Create motorcycle
        m1 = new("Harley", 2019, 80, 0);
        m1.display();
        m1.wheelie();
        
        $display("\n=== Tests Complete ===\n");
        $finish();
    end

endmodule


module test_polymorphism;
    vehicle vehicles[4];

    car c_temp;
    motorcycle m_temp;
    vehicle v_temp;
    initial begin
        $display("\n=== Testing Polymorphism ===\n");
        
        // Create Car and assign to Vehicle array
        c_temp = new("Chevrolet", 1967, 150, 2);
        vehicles[0] = c_temp;
        
        // Create Motorcycle and assign to Vehicle array
        m_temp = new("Harley", 2015, 80, 1);
        vehicles[1] = m_temp;
        
        // Create another Car
        c_temp = new("Ford", 2022, 120, 4);
        vehicles[2] = c_temp;

        v_temp = new("On_Foot", 1995, 5);
        vehicles[3] = v_temp;
        
        $display("--- Demonstrating Polymorphism ---");
        $display("All objects stored in Vehicle[] array, but each calls its own display() method:\n");
        
        // Polymorphic behavior - each object calls its own display() method
        foreach(vehicles[i]) begin
            $display("Vehicle[%0d]:", i);
            vehicles[i].display();
            vehicles[i].accelerate(10);
            $display("");
        end
        
        $display("=== Polymorphism Test Complete ===\n");
        $finish();
    end

endmodule
