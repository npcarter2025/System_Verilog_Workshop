class Employee;
    local int employee_id;
    local string name;
    local real salary;

    protected string department;

    function new(int id, string n, real s);
        employee_id = id;
        name = n;
        salary = s;
    endfunction

    function int get_id();
        return employee_id;
    endfunction

    function string get_name();
        return name;
    endfunction

    function real get_salary();
        return salary;
    endfunction

    function void set_salary(real new_salary);
        if (new_salary <= 0) return;
        salary = new_salary;
    endfunction

    function void give_raise(real percentage);
        if (percentage < 0) return;
        salary = salary * (1.0 + percentage / 100.0);
        $display("%s received a %.2f%% raise. New salary: $%.2f", name, percentage, salary);
    endfunction

    function void display();
        $display("Employee #%0d: %s, Salary: $%.2f", employee_id, name, salary);
    endfunction

endclass

class Manager extends Employee;
    int num_reports;

    function new(int id, string n, real s, string dept, int reports);
        super.new(id, n, s);
        department = dept;
        num_reports = reports;

    endfunction

    function void set_dept(string dept);
        department = dept;
    endfunction

    function string get_dept();
        return department;
    endfunction

    function void display();
        super.display();
        $display("  Department: %s, Reports: %0d", department, num_reports);
    endfunction

endclass

module Employee_tb();

    Employee e1, e2, e3, e4;
    Manager m1, m2, m3, m4;

    initial begin

        e1 = new(1, "e1", 10);
        e2 = new(2, "e2", 20);
        e3 = new(3, "e3", 30);
        e4 = new(4, "e4", 40);

        m1 = new(1, "Mark", 10, "Underwater", 14);
        m2 = new(2, "m2", 20, "front desk", 5);

        $display("%0d", e1.get_salary());

        $display("%0d", m1.get_salary());
        m1.set_salary(1234);
        $display("%0d", m1.get_salary());

        m1.give_raise(100);
        $display("%0d", m1.get_salary());

        $display("%s works in %s Department", m1.get_name(), m1.get_dept());

        $finish();


    end

endmodule
