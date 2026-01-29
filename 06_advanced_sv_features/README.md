# 06 - Advanced SystemVerilog Features

This directory covers advanced SystemVerilog language features that distinguish it from traditional Verilog. These features enable object-oriented programming, powerful testbench construction, and sophisticated design techniques.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Topics Covered](#topics-covered)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

SystemVerilog extends Verilog with powerful features for both design and verification:
- **OOP**: Classes, inheritance, polymorphism
- **Data types**: Dynamic arrays, queues, associative arrays, structs, unions
- **Interfaces**: Encapsulate signals and protocols
- **Randomization**: Constrained random stimulus generation
- **Coverage**: Functional coverage specification

---

## Directory Structure

```
06_advanced_sv_features/
├── README.md
├── classes_oop/
│   ├── basic_class.sv
│   ├── inheritance.sv
│   ├── polymorphism.sv
│   ├── virtual_methods.sv
│   ├── abstract_class.sv
│   └── README.md
├── interfaces/
│   ├── basic_interface.sv
│   ├── modports.sv
│   ├── clocking_blocks.sv
│   ├── virtual_interface.sv
│   └── README.md
├── data_types/
│   ├── dynamic_arrays.sv
│   ├── queues.sv
│   ├── associative_arrays.sv
│   ├── structs_unions.sv
│   ├── typedef_enum.sv
│   └── README.md
├── randomization/
│   ├── basic_randomization.sv
│   ├── constraints.sv
│   ├── pre_post_randomize.sv
│   ├── rand_mode.sv
│   └── README.md
├── packages/
│   ├── package_example.sv
│   ├── import_export.sv
│   └── README.md
├── parameterization/
│   ├── parameter_types.sv
│   ├── parameter_classes.sv
│   └── README.md
├── tasks_functions/
│   ├── automatic_static.sv
│   ├── ref_arguments.sv
│   ├── default_arguments.sv
│   └── README.md
└── design_patterns/
    ├── singleton.sv
    ├── factory.sv
    ├── observer.sv
    └── README.md
```

---

## Topics Covered

### 1. Classes and OOP

#### **Basic Class**
```systemverilog
class packet;
    // Properties
    bit [31:0] addr;
    bit [7:0]  data[];
    
    // Constructor
    function new(int size = 8);
        data = new[size];
    endfunction
    
    // Methods
    function void display();
        $display("Addr: %h, Data size: %0d", addr, data.size());
    endfunction
endclass

// Usage
packet pkt = new(16);
pkt.addr = 32'h1000;
pkt.display();
```

#### **Inheritance**
```systemverilog
class base_packet;
    bit [31:0] addr;
    
    virtual function void display();
        $display("Base: addr=%h", addr);
    endfunction
endclass

class extended_packet extends base_packet;
    bit [7:0] data;
    
    // Override
    virtual function void display();
        super.display();  // Call parent
        $display("Extended: data=%h", data);
    endfunction
endclass
```

#### **Polymorphism**
```systemverilog
base_packet pkt_handle;
extended_packet ext_pkt = new();

pkt_handle = ext_pkt;  // Upcasting
pkt_handle.display();  // Calls extended_packet::display()

// Downcasting
extended_packet ext_pkt2;
$cast(ext_pkt2, pkt_handle);
```

---

### 2. Interfaces

Interfaces encapsulate signals, timing, and protocol:

```systemverilog
interface axi_if(input logic clk, input logic rst_n);
    logic [31:0] awaddr;
    logic        awvalid;
    logic        awready;
    logic [31:0] wdata;
    logic        wvalid;
    logic        wready;
    
    // Modports (directional ports)
    modport master (
        output awaddr, awvalid, wdata, wvalid,
        input  awready, wready
    );
    
    modport slave (
        input  awaddr, awvalid, wdata, wvalid,
        output awready, wready
    );
    
    // Clocking block for testbench
    clocking cb @(posedge clk);
        output awaddr, awvalid;
        input  awready;
    endclocking
    
    // Tasks in interface
    task automatic write(input [31:0] addr, data);
        @(cb);
        cb.awaddr  <= addr;
        cb.awvalid <= 1'b1;
        @(cb);
        wait(cb.awready);
        cb.awvalid <= 1'b0;
    endtask
endinterface

// Module using interface
module master(axi_if.master axi);
    // Use axi.awaddr, axi.awvalid, etc.
endmodule

// Testbench
module tb;
    logic clk, rst_n;
    axi_if axi(clk, rst_n);
    
    master dut(.axi(axi.master));
    
    initial begin
        axi.write(32'h1000, 32'hDEAD);
    end
endmodule
```

---

### 3. Advanced Data Types

#### **Dynamic Arrays**
```systemverilog
int dyn_array[];  // Declare
dyn_array = new[10];  // Allocate
dyn_array[5] = 42;

// Resize
dyn_array = new[20](dyn_array);  // Copy old data
```

#### **Queues**
```systemverilog
int queue[$];  // Unbounded queue

queue.push_back(10);   // Add to end
queue.push_front(5);   // Add to front
int value = queue.pop_back();   // Remove from end
int size = queue.size();

// Bounded queue
int bounded_q[$:15];  // Max 16 elements
```

#### **Associative Arrays**
```systemverilog
// Indexed by string
int aa[string];
aa["john"] = 25;
aa["mary"] = 30;

if (aa.exists("john"))
    $display("John's age: %0d", aa["john"]);

// Indexed by int (sparse)
bit [7:0] sparse[int];
sparse[100] = 8'hAA;
sparse[1000000] = 8'hBB;  // No storage for 0-999999

// Methods
int n = aa.num();  // Number of entries
aa.delete("john");  // Delete entry
aa.first(key);      // Get first key
aa.next(key);       // Get next key
```

#### **Structs and Unions**
```systemverilog
// Struct (all fields present)
typedef struct packed {
    bit [3:0]  opcode;
    bit [11:0] addr;
    bit [15:0] data;
} instruction_t;

instruction_t instr;
instr.opcode = 4'b0010;

// Union (fields share storage)
typedef union {
    int   i;
    real  f;
    bit [31:0] bits;
} data_union_t;

data_union_t u;
u.i = 42;
$display("As bits: %b", u.bits);
```

#### **Typedef and Enum**
```systemverilog
// Typedef
typedef bit [31:0] word_t;
typedef byte unsigned ubyte_t;

// Enum
typedef enum {IDLE, ACTIVE, DONE} state_t;
state_t current_state = IDLE;

// Enum with explicit values
typedef enum bit [1:0] {
    READ  = 2'b00,
    WRITE = 2'b01,
    IDLE  = 2'b10
} command_t;

// Methods
$display("State name: %s", current_state.name());
int num = current_state.num();  // Number of enum members
```

---

### 4. Randomization

```systemverilog
class rand_packet;
    rand bit [7:0]  length;
    rand bit [31:0] addr;
    randc bit [3:0] id;  // randc = random cyclic (no repeat until all values)
    
    // Constraints
    constraint c_length {
        length inside {[8:128]};
        length % 4 == 0;  // Multiple of 4
    }
    
    constraint c_addr {
        addr[1:0] == 2'b00;  // Word aligned
    }
    
    // Functions
    function void pre_randomize();
        $display("Before randomization");
    endfunction
    
    function void post_randomize();
        $display("After randomization: length=%0d", length);
    endfunction
endclass

// Usage
rand_packet pkt = new();
assert(pkt.randomize());  // Randomize

// Inline constraints
assert(pkt.randomize() with {
    length == 64;
    addr inside {[32'h1000:32'h2000]};
});

// Disable randomization
pkt.length.rand_mode(0);  // Don't randomize length

// Disable constraints
pkt.c_length.constraint_mode(0);  // Disable constraint
```

---

### 5. Packages

Organize and share code:

```systemverilog
// my_pkg.sv
package my_pkg;
    typedef enum {RED, GREEN, BLUE} color_t;
    
    class my_class;
        int value;
    endclass
    
    function int add(int a, int b);
        return a + b;
    endfunction
endpackage

// Usage in another file
import my_pkg::*;  // Import all

// Or selective import
import my_pkg::color_t;
import my_pkg::add;

// Or use qualified name
my_pkg::color_t my_color;
```

---

### 6. Parameterization

#### **Parameter Types**
```systemverilog
module fifo #(
    parameter int DEPTH = 16,
    parameter int WIDTH = 32,
    parameter type T = logic [WIDTH-1:0],  // Type parameter
    localparam ADDR_WIDTH = $clog2(DEPTH)  // Computed
) (
    input  T     data_in,
    output T     data_out,
    // ...
);
```

#### **Parameterized Classes**
```systemverilog
class generic_queue #(type T = int, int MAX_SIZE = 16);
    T items[$];
    
    function void push(T item);
        if (items.size() < MAX_SIZE)
            items.push_back(item);
    endfunction
    
    function T pop();
        return items.pop_front();
    endfunction
endclass

// Usage
generic_queue#(bit [7:0], 32) byte_queue = new();
generic_queue#(string) str_queue = new();
```

---

### 7. Tasks and Functions

#### **Automatic vs Static**
```systemverilog
// Static (default) - single copy shared across calls
task static_task();
    int count = 0;  // Shared across concurrent calls!
    count++;
endtask

// Automatic - each call gets own copy (reentrant)
task automatic auto_task();
    int count = 0;  // Separate for each call
    count++;
endtask
```

#### **Reference Arguments**
```systemverilog
// Pass by value (default)
function void increment(int value);
    value++;  // Original unchanged
endfunction

// Pass by reference
function void increment_ref(ref int value);
    value++;  // Original modified
endfunction
```

#### **Default Arguments**
```systemverilog
function void init(int size = 10, bit clear = 1);
    // ...
endfunction

init();           // Uses defaults: size=10, clear=1
init(20);         // size=20, clear=1
init(20, 0);      // size=20, clear=0
init(.clear(0));  // size=10, clear=0 (named argument)
```

---

### 8. Clocking Blocks

Separate timing from functionality:

```systemverilog
interface bus_if(input logic clk);
    logic [31:0] data;
    logic        valid;
    logic        ready;
    
    // Clocking block for testbench
    clocking cb @(posedge clk);
        default input #1ns output #2ns;  // Skew
        output data, valid;
        input  ready;
    endclocking
    
    // Driver uses clocking block
    modport driver (clocking cb);
endinterface

// Testbench
module tb;
    bus_if bus(clk);
    
    initial begin
        // Clean timing, no race conditions
        @(bus.cb);
        bus.cb.data  <= 32'h1234;
        bus.cb.valid <= 1'b1;
        @(bus.cb);
        wait(bus.cb.ready);
    end
endmodule
```

---

### 9. Casting

```systemverilog
// Static cast (compile-time check)
int i;
byte b;
b = byte'(i);  // Explicit cast

// Dynamic cast (run-time check)
base_class base_obj;
derived_class derived_obj;

// $cast returns 1 on success, 0 on failure
if ($cast(derived_obj, base_obj))
    $display("Cast successful");
else
    $display("Cast failed");
```

---

### 10. Virtual Interfaces

For testbenches that need to pass interfaces:

```systemverilog
class driver;
    virtual axi_if vif;  // Virtual interface
    
    function new(virtual axi_if vif);
        this.vif = vif;
    endfunction
    
    task drive();
        @(vif.cb);
        vif.cb.awaddr <= 32'h1000;
    endtask
endclass

module tb;
    axi_if axi(clk, rst_n);
    driver drv;
    
    initial begin
        drv = new(axi);  // Pass interface to class
        drv.drive();
    end
endmodule
```

---

## Key Concepts Summary

| Feature | Purpose | Syntax Example |
|---------|---------|----------------|
| **Classes** | OOP, encapsulation | `class foo; ... endclass` |
| **Inheritance** | Code reuse | `class bar extends foo;` |
| **Interfaces** | Signal grouping | `interface my_if; ... endinterface` |
| **Modports** | Directional ports | `modport master(output a, input b);` |
| **Dynamic Arrays** | Runtime sizing | `int arr[]; arr = new[10];` |
| **Queues** | FIFO operations | `int q[$]; q.push_back(5);` |
| **Assoc. Arrays** | Sparse storage | `int aa[string]; aa["key"] = 5;` |
| **Constraints** | Random limits | `constraint c { x inside {[0:100]}; }` |
| **Packages** | Code organization | `package pkg; ... endpackage` |
| **Type Parameters** | Generic programming | `module m #(type T);` |

---

## Common Use Cases

### Design
- **Interfaces**: Clean module connections
- **Structs/Unions**: Complex data types
- **Parameters**: Configurable designs
- **Packages**: Shared definitions

### Verification
- **Classes**: Transaction objects, components
- **Randomization**: Stimulus generation
- **Constraints**: Directed-random testing
- **Queues**: Mailboxes, scoreboards
- **Virtual Interfaces**: Pass to classes
- **Clocking Blocks**: Race-free testbenches

---

## Learning Path

1. **Week 1**: Classes, inheritance, basic OOP
2. **Week 2**: Interfaces, modports, clocking blocks
3. **Week 3**: Advanced data types (queues, associative arrays)
4. **Week 4**: Randomization and constraints
5. **Week 5**: Packages and parameterization
6. **Week 6**: Design patterns and best practices

---

## Best Practices

### Classes
✅ Use `virtual` for methods that may be overridden  
✅ Call `super.new()` in constructors  
✅ Use deep copy when needed (not just handle copy)

### Interfaces
✅ Use modports for directional clarity  
✅ Use clocking blocks in testbenches  
✅ Group related signals together

### Randomization
✅ Use `randc` for exhaustive coverage  
✅ Keep constraints simple and readable  
✅ Check `randomize()` return value

### Data Types
✅ Use queues for dynamic FIFO operations  
✅ Use associative arrays for sparse data  
✅ Use packed structs for bus interfaces

---

## Common Pitfalls

1. **Shallow copy**: `pkt2 = pkt1` copies handle, not data
   - Solution: Implement `copy()` method
2. **Missing virtual**: Polymorphism won't work
3. **Queue bounds**: `$` queues can grow unbounded
4. **Interface timing**: Be careful with combinational logic in interfaces
5. **Constraint conflicts**: Over-constrained = randomization fails

---

## Code Examples

Each subdirectory contains:
- Working examples with comments
- Testbenches demonstrating usage
- Common patterns and anti-patterns
- Best practice recommendations

---

## Tools Support

All major simulators support SystemVerilog:
- **Synopsys VCS**: Full support
- **Cadence Xcelium**: Full support  
- **Mentor Questa**: Full support
- **Verilator**: Partial (improving)

Compile with:
```bash
vcs -sverilog file.sv
xrun -sv file.sv
vlog -sv file.sv
```

---

## References

### Books
- **"SystemVerilog for Verification"** - Chris Spear & Greg Tumbush
- **"SystemVerilog for Design"** - Stuart Sutherland
- **"Advanced UVM"** - Brian Hunter (for class usage in UVM)

### Standards
- **IEEE 1800-2017**: SystemVerilog Language Reference Manual

### Online
- **ChipVerify**: https://www.chipverify.com/systemverilog/
- **ASIC World**: http://www.asic-world.com/systemverilog/
- **Verification Guide**: https://verificationguide.com/systemverilog/

---

**Last Updated**: January 2026  
**Maintainer**: System Verilog Workshop
