# SystemVerilog OOP Classes - Practice Tasks

This document contains 10 simple tasks to help you practice the basics of SystemVerilog Object-Oriented Programming (OOP) classes. Each task builds upon previous concepts and covers fundamental OOP principles in SystemVerilog.

---

## Task 1: Basic Class Definition
**Objective:** Create a simple class with basic properties and methods.

Create a class called `Counter` with:
- A private integer property `count` initialized to 0
- A public method `increment()` that increases `count` by 1
- A public method `getCount()` that returns the current value of `count`
- A public method `reset()` that sets `count` back to 0

**Test:** Instantiate the class, call `increment()` a few times, verify the count, then reset it.

---

## Task 2: Constructor and Destructor
**Objective:** Implement class constructors and destructors.

Extend the `Counter` class from Task 1 to include:
- A constructor (`new()`) that accepts an optional initial value parameter
- A destructor that prints a message when the object is destroyed
- If no initial value is provided, default to 0

**Test:** Create multiple counter instances with different initial values and observe the constructor/destructor behavior.

---

## Task 3: Class Properties and Access Modifiers
**Objective:** Practice using different access modifiers (public, protected, private).

Create a class called `BankAccount` with:
- A private property `balance` (real type)
- A protected property `accountNumber` (int)
- A public property `accountName` (string)
- Public methods: `deposit(amount)`, `withdraw(amount)`, `getBalance()`
- A protected method `validateTransaction(amount)` that returns 1 if amount > 0, else 0

**Test:** Create an account, make deposits and withdrawals, and verify access restrictions work correctly.

---

## Task 4: Static Properties and Methods
**Objective:** Understand static class members.

Create a class called `Student` with:
- Instance properties: `name` (string), `studentID` (int), `grade` (real)
- A static property `totalStudents` that tracks the number of student instances
- A static method `getTotalStudents()` that returns the total count
- Increment `totalStudents` in the constructor
- Decrement `totalStudents` in the destructor

**Test:** Create multiple student objects and verify the static counter tracks them correctly.

---

## Task 5: Class Methods with Parameters and Return Values
**Objective:** Practice methods with various parameter types and return values.

Create a class called `Calculator` with:
- Methods: `add(a, b)`, `subtract(a, b)`, `multiply(a, b)`, `divide(a, b)`
- A method `power(base, exponent)` that calculates base^exponent
- A method `getStatistics()` that returns a struct containing: sum, product, and average of all operations performed
- Track operation counts internally

**Test:** Perform various calculations and verify results and statistics.

---

## Task 6: Class Inheritance - Basic
**Objective:** Create a base class and derived class.

Create a base class `Vehicle` with:
- Properties: `make` (string), `model` (string), `year` (int)
- Methods: `start()`, `stop()`, `getInfo()` (returns a formatted string)

Create a derived class `Car` that extends `Vehicle`:
- Additional property: `numDoors` (int)
- Override `getInfo()` to include the number of doors
- Add a method `honk()` specific to cars

**Test:** Create instances of both classes and verify inheritance works correctly.

---

## Task 7: Virtual Methods and Polymorphism
**Objective:** Implement virtual methods for polymorphism.

Extend Task 6:
- Make `getInfo()` virtual in the `Vehicle` base class
- Create another derived class `Motorcycle` that extends `Vehicle`
- Override `getInfo()` in both `Car` and `Motorcycle`
- Create a method that accepts a `Vehicle` handle and calls `getInfo()` on it

**Test:** Use polymorphism to call `getInfo()` on different vehicle types through a base class handle.

---

## Task 8: Abstract Classes and Pure Virtual Methods
**Objective:** Create abstract base classes.

Create an abstract class `Shape` with:
- A pure virtual method `getArea()` that returns a real
- A pure virtual method `getPerimeter()` that returns a real
- A concrete method `printInfo()` that calls the virtual methods

Create concrete classes `Rectangle` and `Circle` that extend `Shape`:
- Implement the pure virtual methods appropriately
- Add necessary properties (e.g., `width`, `height` for Rectangle; `radius` for Circle)

**Test:** Create instances of concrete classes and verify abstract class behavior.

---

## Task 9: Class Arrays and Dynamic Objects
**Objective:** Work with arrays of class objects and dynamic allocation.

Create a class `Employee` with:
- Properties: `name` (string), `employeeID` (int), `salary` (real)
- Methods: `setSalary(amount)`, `getSalary()`, `getInfo()`

In your testbench:
- Create a dynamic array of `Employee` handles
- Allocate 5 employee objects
- Populate them with different data
- Calculate and display the average salary
- Properly deallocate all objects

**Test:** Verify dynamic allocation and array handling works correctly.

---

## Task 10: Class Composition and Aggregation
**Objective:** Create classes that contain other class objects.

Create a class `Engine` with:
- Properties: `horsepower` (int), `cylinders` (int)
- Methods: `start()`, `stop()`, `getSpecs()`

Create a class `Wheel` with:
- Properties: `size` (int), `pressure` (real)
- Methods: `inflate(amount)`, `getInfo()`

Create a class `Automobile` that:
- Contains an `Engine` object
- Contains an array of 4 `Wheel` objects
- Has methods: `startCar()`, `checkTires()`, `getFullSpecs()`
- Properly initializes all components in the constructor

**Test:** Create an `Automobile` instance and verify composition works correctly.

---

## Tips for Practice

1. **Start Simple:** Begin with Task 1 and work through sequentially
2. **Test Thoroughly:** Write testbenches for each task to verify correctness
3. **Experiment:** Try variations and modifications to deepen understanding
4. **Read Errors:** SystemVerilog compiler errors are helpful - learn from them
5. **Use Comments:** Document your code to reinforce understanding

## Additional Challenges (After Completing All Tasks)

- Add error handling to methods (e.g., prevent negative balances, division by zero)
- Implement operator overloading for your classes
- Create interfaces and implement them in your classes
- Practice using `$cast()` for safe type conversions
- Explore parameterized classes (generics)

---

**Good luck with your SystemVerilog OOP practice!**

