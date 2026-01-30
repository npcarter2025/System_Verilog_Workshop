


class Student;
    string name;
    int roll_number;
    real gpa;

    static int student_count;
    static real total_gpa;

    function new(string n, real g);
        name = n;
        gpa = g;
        roll_number = $urandom_range(100,10);

        student_count++;
        total_gpa += g;
    endfunction

    static function int get_student_count();
        return student_count;
    endfunction

    static function real get_average_gpa();
        return (total_gpa / student_count);
    endfunction
    function void display();
        $display("Name: %s, Roll Number: %0d, GPA: %.3f", name, roll_number, gpa);
    endfunction
endclass

module student_tb;
    Student s1, s2, s3;

    initial begin
        s1 = new("Alice", 3.855);
        s1.display();
        s2 = new("Bob", 3.111);
        s2.display();
        s3 = new("Carl", 1.000);
        s3.display();

        $display("Total students: %0d", Student::get_student_count());
        $display("Average GPA: %0.3f", Student::get_average_gpa());

        $finish();

    end
endmodule


