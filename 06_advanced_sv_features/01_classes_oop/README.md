# SystemVerilog OOP Exercises

Practical exercises to master Object-Oriented Programming in SystemVerilog. Work through these exercises progressively to build your OOP skills.

---

## Table of Contents

1. [Basic Classes](#exercise-1-basic-classes)
2. [Constructors and Methods](#exercise-2-constructors-and-methods)
3. [Inheritance](#exercise-3-inheritance)
4. [Polymorphism](#exercise-4-polymorphism)
5. [Virtual Methods](#exercise-5-virtual-methods)
6. [Abstract Classes](#exercise-6-abstract-classes)
7. [Encapsulation](#exercise-7-encapsulation)
8. [Static Members](#exercise-8-static-members)
9. [Copy and Clone](#exercise-9-copy-and-clone)
10. [Parameterized Classes](#exercise-10-parameterized-classes)

---

## Exercise 1: Basic Classes

**Goal**: Create a simple class and instantiate objects.

### Task
Create a `BankAccount` class with:
- Properties: `account_number` (int), `balance` (real), `owner_name` (string)
- A constructor that initializes all properties
- A `display()` method that prints account details

### Expected Output
```
Account: 12345, Owner: John Doe, Balance: $1000.50
```

### Solution Template
```systemverilog
class BankAccount;
    // TODO: Add properties
    
    // TODO: Add constructor
    
    // TODO: Add display method
endclass

module test_bank_account;
    initial begin
        // TODO: Create account object
        // TODO: Call display method
    end
endmodule
```

### Hints
- Use `function new()` for the constructor
- Use `$sformatf` for string formatting
- Remember to use `new()` when creating objects

---

## Exercise 2: Constructors and Methods

**Goal**: Practice different constructor patterns and method types.

### Task
Create a `Rectangle` class with:
- Properties: `width`, `height`
- Default constructor (sets width=1, height=1)
- Parameterized constructor (takes width and height)
- Method: `area()` - returns area
- Method: `perimeter()` - returns perimeter
- Method: `is_square()` - returns 1 if square, 0 otherwise
- Method: `scale(factor)` - multiplies dimensions by factor

### Expected Behavior
```systemverilog
Rectangle r1 = new();              // 1x1 rectangle
Rectangle r2 = new(5, 3);          // 5x3 rectangle
int a = r2.area();                 // Returns 15
r2.scale(2);                       // Now 10x6
```

### Challenge
Add a `compare(Rectangle other)` method that returns:
- 1 if this rectangle is larger
- 0 if equal
- -1 if smaller

---

## Exercise 3: Inheritance

**Goal**: Understand inheritance and method overriding.

### Task
Create a class hierarchy for vehicles:

**Base Class: Vehicle**
- Properties: `brand` (string), `year` (int), `speed` (int)
- Constructor
- Method: `accelerate(amount)` - increases speed
- Method: `brake(amount)` - decreases speed
- Method: `display()` - shows vehicle info

**Derived Class: Car extends Vehicle**
- Additional property: `num_doors` (int)
- Override `display()` to include number of doors
- Add method: `honk()` - prints "Beep beep!"

**Derived Class: Motorcycle extends Vehicle**
- Additional property: `has_sidecar` (bit)
- Override `display()` to include sidecar info
- Add method: `wheelie()` - prints "Doing a wheelie!"

### Expected Output
```
Car: Toyota 2020, Speed: 60 mph, Doors: 4
Motorcycle: Harley 2019, Speed: 80 mph, Sidecar: No
```

### Challenge
Add a `Truck` class that extends `Car` and adds `cargo_capacity`.

---

## Exercise 4: Polymorphism

**Goal**: Use parent class handles to reference child objects.

### Task
Using the Vehicle hierarchy from Exercise 3:

1. Create an array of `Vehicle` handles
2. Fill it with different vehicle types (Car, Motorcycle)
3. Loop through and call `display()` on each
4. Demonstrate polymorphic behavior

### Code Template
```systemverilog
module test_polymorphism;
    Vehicle vehicles[3];
    
    initial begin
        vehicles[0] = new(...);  // Create Car
        vehicles[1] = new(...);  // Create Motorcycle
        vehicles[2] = new(...);  // Create Car
        
        foreach(vehicles[i]) begin
            vehicles[i].display();
            vehicles[i].accelerate(10);
        end
    end
endmodule
```

### Challenge
Create a `race()` function that takes an array of Vehicles and finds the fastest one.

---

## Exercise 5: Virtual Methods

**Goal**: Master virtual methods and dynamic binding.

### Task
Create a shape hierarchy:

**Base Class: Shape** (with virtual methods)
- Virtual method: `area()` - returns 0.0 in base
- Virtual method: `perimeter()` - returns 0.0 in base
- Virtual method: `draw()` - prints "Generic shape"

**Derived Classes:**
- `Circle`: radius property, override area/perimeter/draw
- `Rectangle`: width/height properties, override all methods
- `Triangle`: base/height properties, override all methods

### Key Requirement
All methods in base class must be declared `virtual`.

### Test Code
```systemverilog
Shape shapes[3];
shapes[0] = new Circle(5);
shapes[1] = new Rectangle(4, 6);
shapes[2] = new Triangle(3, 4);

foreach(shapes[i]) begin
    $display("Area: %f, Perimeter: %f", 
             shapes[i].area(), 
             shapes[i].perimeter());
    shapes[i].draw();
end
```

### Expected Output
```
Area: 78.540000, Perimeter: 31.416000
Drawing a circle...
Area: 24.000000, Perimeter: 20.000000
Drawing a rectangle...
Area: 6.000000, Perimeter: 12.000000
Drawing a triangle...
```

---

## Exercise 6: Abstract Classes

**Goal**: Create abstract base classes with pure virtual methods.

### Task
Create an abstract `Animal` class hierarchy:

**Abstract Class: Animal**
- Properties: `name`, `age`
- Pure virtual method: `make_sound()` - must be overridden
- Pure virtual method: `move()` - must be overridden
- Concrete method: `display_info()` - can be used as-is

**Concrete Classes:**
- `Dog`: implements `make_sound()` → "Woof!", `move()` → "Running"
- `Cat`: implements `make_sound()` → "Meow!", `move()` → "Prowling"
- `Bird`: implements `make_sound()` → "Chirp!", `move()` → "Flying"

### Constraints
- Animal class cannot be instantiated directly
- All derived classes MUST implement the pure virtual methods

### Code Template
```systemverilog
virtual class Animal;
    string name;
    int age;
    
    function new(string n, int a);
        name = n;
        age = a;
    endfunction
    
    pure virtual function void make_sound();
    pure virtual function void move();
    
    function void display_info();
        $display("%s is %0d years old", name, age);
    endfunction
endclass

class Dog extends Animal;
    // TODO: Implement required methods
endclass
```

### Challenge
Add a `Zoo` class that manages an array of Animals and can make all animals perform actions.

---

## Exercise 7: Encapsulation

**Goal**: Use local/protected members and access methods.

### Task
Create an `Employee` class with proper encapsulation:

**Private Properties:**
- `local int employee_id`
- `local string name`
- `local real salary`

**Public Methods:**
- `function new(int id, string n, real s)`
- `function int get_id()`
- `function string get_name()`
- `function real get_salary()`
- `function void set_salary(real new_salary)` - with validation (>0)
- `function void give_raise(real percentage)`

### Requirements
- Direct access to properties should NOT be possible
- salary can only be set through methods
- Implement validation in setter methods

### Test Code
```systemverilog
Employee emp = new(101, "Alice", 50000);
$display("Salary: $%0f", emp.get_salary());  // OK
emp.give_raise(10);  // 10% raise
// emp.salary = 100000;  // Should cause ERROR!
```

### Challenge
Add a `protected` property `department` and create a `Manager` subclass that can access it.

---

## Exercise 8: Static Members

**Goal**: Understand class-level vs instance-level members.

### Task
Create a `Student` class with student tracking:

**Properties:**
- Instance: `string name`, `int roll_number`, `real gpa`
- Static: `int student_count` - tracks total students created
- Static: `real total_gpa` - sum of all GPAs

**Methods:**
- Instance: `function new(string n, real g)`
- Static: `function int get_student_count()`
- Static: `function real get_average_gpa()`
- Instance: `function void display()`

### Requirements
- Auto-assign roll numbers (1, 2, 3, ...)
- Track count and average GPA across ALL students
- Static methods should be callable without an object

### Test Code
```systemverilog
Student s1 = new("Alice", 3.8);
Student s2 = new("Bob", 3.5);
Student s3 = new("Carol", 3.9);

$display("Total students: %0d", Student::get_student_count());
$display("Average GPA: %0.2f", Student::get_average_gpa());
```

### Expected Output
```
Total students: 3
Average GPA: 3.73
```

---

## Exercise 9: Copy and Clone

**Goal**: Implement shallow and deep copy.

### Task
Create a `Course` class:

**Properties:**
- `string course_name`
- `int credits`
- `int enrolled_students[]` - dynamic array

**Methods:**
- `function new(string name, int cred)`
- `function void enroll_student(int student_id)`
- `function Course shallow_copy()` - copies object, shares array
- `function Course deep_copy()` - copies everything, new array
- `function void display()`

### Test Scenario
```systemverilog
Course c1 = new("Math", 3);
c1.enroll_student(101);
c1.enroll_student(102);

Course c2 = c1.shallow_copy();
Course c3 = c1.deep_copy();

c1.enroll_student(103);

// c2 should show 101, 102, 103 (shares array)
// c3 should show 101, 102 (independent array)
```

### Challenge
Implement a `clone()` method that creates a deep copy and compare it with copy constructor approach.

---

## Exercise 10: Parameterized Classes

**Goal**: Create generic/reusable classes with parameters.

### Task
Create a generic `Stack` class:

**Template:**
```systemverilog
class Stack #(type T = int, int SIZE = 10);
    local T data[SIZE];
    local int top;
    
    function new();
        top = -1;
    endfunction
    
    function bit push(T item);
        // TODO: Implement
    endfunction
    
    function bit pop(output T item);
        // TODO: Implement
    endfunction
    
    function bit is_empty();
        return (top == -1);
    endfunction
    
    function bit is_full();
        return (top == SIZE-1);
    endfunction
    
    function int size();
        return top + 1;
    endfunction
endclass
```

### Test Cases
```systemverilog
// Stack of integers
Stack #(int, 5) int_stack = new();
int_stack.push(10);
int_stack.push(20);

// Stack of strings
Stack #(string, 3) str_stack = new();
str_stack.push("Hello");
str_stack.push("World");

// Stack of custom objects
Stack #(BankAccount, 10) account_stack = new();
```

### Challenge
Create a generic `Queue` class with `enqueue()` and `dequeue()` methods.

---

## Bonus Exercise: Design Pattern - Factory

**Goal**: Implement the Factory design pattern.

### Task
Create a packet factory for network simulation:

**Base Class: Packet** (abstract)
- Properties: `bit [31:0] src_addr`, `bit [31:0] dest_addr`
- Pure virtual: `function void generate()`
- Pure virtual: `function void display()`

**Derived Classes:**
- `TCPPacket`: Add `bit [15:0] src_port`, `bit [15:0] dest_port`
- `UDPPacket`: Add `bit [15:0] checksum`
- `ICMPPacket`: Add `bit [7:0] type`, `bit [7:0] code`

**Factory Class:**
```systemverilog
class PacketFactory;
    typedef enum {TCP, UDP, ICMP} packet_type_e;
    
    static function Packet create_packet(packet_type_e ptype);
        case (ptype)
            TCP:  return new TCPPacket();
            UDP:  return new UDPPacket();
            ICMP: return new ICMPPacket();
        endcase
    endfunction
endclass
```

### Usage
```systemverilog
Packet pkt = PacketFactory::create_packet(PacketFactory::TCP);
pkt.generate();
pkt.display();
```

---

## Tips for Success

1. **Start Simple**: Begin with Exercise 1 and work sequentially
2. **Compile Often**: Use VCS/Questa to catch syntax errors early
3. **Test Thoroughly**: Write comprehensive test cases
4. **Read Errors**: SystemVerilog error messages are helpful
5. **Experiment**: Try variations of the exercises
6. **Document**: Add comments explaining your design choices

---

## Running Your Code

### With VCS
```bash
vcs -sverilog -full64 your_file.sv -o simv
./simv
```

### With Questa/ModelSim
```bash
vlog -sv your_file.sv
vsim -c work.your_module -do "run -all; quit"
```

---

## Common OOP Mistakes to Avoid

1. **Forgetting `new()`**: Objects must be constructed
   ```systemverilog
   BankAccount acc;  // NULL handle
   acc = new();      // Now it's valid
   ```

2. **Not calling `super.new()`**: In derived classes
   ```systemverilog
   class Dog extends Animal;
       function new(string n);
           super.new(n);  // MUST call parent constructor
       endfunction
   endclass
   ```

3. **Missing `virtual` keyword**: For polymorphism
   ```systemverilog
   virtual function void display();  // Allows override
   ```

4. **Shallow copy issues**: Array/object members share references
   ```systemverilog
   // Need deep copy for dynamic arrays
   new_array = new[old_array.size()];
   foreach(old_array[i]) new_array[i] = old_array[i];
   ```

---

## Additional Challenges

Once you complete all exercises, try these advanced challenges:

1. **Observer Pattern**: Implement event notification system
2. **Singleton Pattern**: Ensure only one instance of a class
3. **Iterator Pattern**: Create custom iteration over collection
4. **Command Pattern**: Encapsulate actions as objects
5. **State Machine**: Model FSM using OOP principles

---

## Resources

- SystemVerilog LRM (IEEE 1800-2017)
- "SystemVerilog for Verification" by Chris Spear
- Verification Academy tutorials
- DVCon papers on verification methodologies

---

## Solutions

Solutions are provided in separate files:
- `solutions/exercise_01_solution.sv`
- `solutions/exercise_02_solution.sv`
- ... etc

Try solving exercises yourself before looking at solutions!

Happy coding! 🚀
