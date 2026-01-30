# SystemVerilog Advanced Data Types - Practice Exercises

This directory contains exercises to help you master SystemVerilog's advanced data types. Work through these exercises sequentially to build your understanding from basic to advanced concepts.

---

## Table of Contents

1. [Dynamic Arrays](#1-dynamic-arrays)
2. [Queues](#2-queues)
3. [Associative Arrays](#3-associative-arrays)
4. [Structs and Unions](#4-structs-and-unions)
5. [Typedef and Enums](#5-typedef-and-enums)
6. [Mixed Exercises](#6-mixed-exercises)
7. [Challenge Problems](#7-challenge-problems)

---

## 1. Dynamic Arrays

### Exercise 1.1: Basic Dynamic Array Operations
Create a testbench module that:
- Declares a dynamic array of integers
- Allocates space for 10 elements
- Fills it with values 0-9
- Displays the array size and contents
- Deallocates the array

### Exercise 1.2: Array Resizing
Write a testbench that:
- Creates a dynamic array of 5 elements with values [10, 20, 30, 40, 50]
- Resizes the array to 8 elements while preserving existing data
- Fills the new elements (indices 5-7) with values [60, 70, 80]
- Displays the contents before and after resizing

### Exercise 1.3: Memory Calculator
Create a testbench that:
- Takes an input parameter for array size
- Allocates a dynamic array of bit [31:0] with that size
- Fills it with random values
- Calculates and displays: sum, average, min, and max values
- Hint: Use `$urandom()` for random values

### Exercise 1.4: Array Copy
Write a program that:
- Creates a dynamic array A of 10 integers with sequential values
- Allocates a new array B of the same size
- Copies all elements from A to B
- Modifies B (multiply each element by 2)
- Displays both arrays to verify A is unchanged

### Exercise 1.5: 2D Dynamic Array
Create a testbench with:
- A dynamic 2D array (array of dynamic arrays)
- Allocate it as a 4x3 matrix
- Fill it with multiplication table values (row * col)
- Display it in matrix format

---

## 2. Queues

### Exercise 2.1: Basic Queue Operations
Create a testbench that demonstrates:
- Creating an unbounded queue of integers
- Using `push_back()` to add 5 elements
- Using `push_front()` to add 2 elements at the beginning
- Using `pop_back()` and `pop_front()` to remove elements
- Display queue contents after each operation

### Exercise 2.2: Queue as FIFO
Implement a FIFO buffer simulation:
- Create a queue to represent a data buffer
- Add 10 data values using `push_back()`
- Remove and process 5 values using `pop_front()`
- Add 3 more values
- Process remaining values
- Display the order of processing

### Exercise 2.3: Queue as Stack
Implement a stack (LIFO) using a queue:
- Push 5 elements onto the stack
- Pop 3 elements from the stack
- Push 2 more elements
- Pop all remaining elements
- Verify LIFO behavior

### Exercise 2.4: Bounded Queue
Create a testbench that:
- Declares a bounded queue with max size 8
- Attempts to push 10 elements
- Checks queue size before each push
- Handles overflow conditions (when queue is full)
- Displays which elements were successfully added

### Exercise 2.5: Queue Methods
Write a program demonstrating:
- `insert()` - insert element at specific position
- `delete()` - remove element at specific position
- Accessing elements using index notation `q[i]`
- Using `foreach` to iterate through queue
- Finding specific values in the queue

### Exercise 2.6: Priority Queue Simulation
Create a simple priority queue:
- Each element is a struct with {priority, data}
- Insert elements at positions based on priority (higher priority at front)
- Implement a function to insert while maintaining priority order
- Process elements in priority order

---

## 3. Associative Arrays

### Exercise 3.1: Basic Associative Array
Create a testbench that:
- Declares an associative array with string keys and integer values
- Adds entries for 5 different names and ages
- Checks if a specific name exists using `exists()`
- Retrieves and displays ages for specific names
- Displays total number of entries using `num()`

### Exercise 3.2: Sparse Memory Model
Implement a sparse memory model:
- Use associative array indexed by `bit [31:0]` (addresses)
- Use `bit [7:0]` for data values
- Write data to addresses: 0x1000, 0x5000, 0xA0000, 0x1000000
- Read back and verify all addresses
- Demonstrate memory efficiency (only 4 entries stored)

### Exercise 3.3: Associative Array Iteration
Write a program that:
- Creates an associative array of student names (string) to scores (int)
- Adds 6-8 students with various scores
- Uses `first()` and `next()` to iterate through all entries
- Calculates average score
- Finds the highest and lowest scores with student names

### Exercise 3.4: Cache Simulation
Simulate a simple cache:
- Use associative array indexed by address
- Implement read operation: check if exists, if not "miss"
- Implement write operation: add to cache
- Keep track of hits and misses
- Test with a sequence of read/write operations

### Exercise 3.5: Deletion and Cleanup
Create a testbench that:
- Populates an associative array with 10 entries
- Deletes specific entries using `delete(key)`
- Attempts to access deleted entries
- Uses `delete()` with no arguments to clear entire array
- Verifies array is empty

### Exercise 3.6: Wildcard Index
Demonstrate associative array with wildcard index `[*]`:
- Create an array that can be indexed by any integral type
- Add entries with different index types/values
- Iterate through and display all entries
- Show flexibility of wildcard indexing

---

## 4. Structs and Unions

### Exercise 4.1: Basic Struct
Define and use a struct:
- Create a struct `packet_t` with fields: address (32-bit), data (8-bit), valid (1-bit)
- Declare a variable of this struct type
- Assign values to each field
- Display all fields
- Create and initialize another packet with different values

### Exercise 4.2: Packed vs Unpacked Structs
Compare packed and unpacked structs:
- Define identical structs, one packed and one unpacked
- Try to access them as a single bit vector (only works for packed)
- Compare memory layout
- Demonstrate when to use each type

### Exercise 4.3: Nested Structs
Create nested structures:
- Define a `header_t` struct with: version, length, checksum
- Define a `payload_t` struct with: data array [10]
- Define a `frame_t` struct containing both header and payload
- Create a frame, initialize all fields including nested ones
- Access nested fields using dot notation

### Exercise 4.4: Array of Structs
Work with struct arrays:
- Define a struct `transaction_t` with: id, address, data, timestamp
- Create a dynamic array of transactions
- Allocate space for 5 transactions
- Fill each transaction with different values
- Search for a transaction with specific id
- Sort by timestamp (implement simple sort)

### Exercise 4.5: Basic Union
Demonstrate union usage:
- Create a union with: int, real, bit [31:0]
- Assign a value to int field
- Read as bit [31:0] to see bit pattern
- Assign real value
- Read as bits again
- Show that fields share same storage

### Exercise 4.6: Tagged Union Pattern
Create a safe union:
- Define an enum `data_type_t` (INT, REAL, BITS)
- Create a struct containing: enum tag + union of types
- Write functions to safely set and get values based on tag
- Demonstrate type-safe access

### Exercise 4.7: Protocol Packet
Design a realistic packet structure:
- Create structs for: Ethernet header, IP header, TCP header
- Create a packed struct combining all three
- Initialize a complete packet
- Access and modify individual header fields
- Display entire packet as hex values

---

## 5. Typedef and Enums

### Exercise 5.1: Basic Typedef
Create typedefs for:
- `byte_t` as unsigned byte
- `word_t` as 32-bit vector
- `addr_t` as 64-bit vector
- Declare variables of each type
- Demonstrate improved code readability

### Exercise 5.2: Complex Typedefs
Define typedefs for:
- A dynamic array of bytes
- A queue of words
- An associative array (string keys to integers)
- Use these types to declare and manipulate data structures

### Exercise 5.3: Basic Enum
Create and use enumerations:
- Define `state_t` enum: IDLE, FETCH, DECODE, EXECUTE, WRITEBACK
- Declare a state variable
- Cycle through all states
- Display state names using `.name()` method
- Demonstrate default incrementing values

### Exercise 5.4: Enum with Explicit Values
Define enums with specific values:
- Create `opcode_t` enum matching your ISA (ADD=0, SUB=1, MUL=2, etc.)
- Create `priority_t` enum: LOW=1, MEDIUM=5, HIGH=10
- Demonstrate accessing the underlying values
- Show that you can cast between enum and integer

### Exercise 5.5: Enum Methods
Explore enum methods:
- Create an enum with 5-6 values
- Use `.first()` to get first value
- Use `.last()` to get last value
- Use `.next()` and `.prev()` to traverse
- Use `.num()` to get number of members
- Create a loop that goes through all enum values

### Exercise 5.6: State Machine
Implement a simple state machine:
- Define states: RESET, INIT, READY, BUSY, DONE, ERROR
- Create logic to transition between states based on inputs
- Use case statement with enum values
- Display current state at each transition
- Show how enums make state machines more readable

### Exercise 5.7: Type Parameters
Create generic typedefs:
- Define a struct template that can hold different data types
- Use typedef to create specific instances (int version, byte version)
- Demonstrate reusability

---

## 6. Mixed Exercises

These exercises combine multiple data types to solve realistic problems.

### Exercise 6.1: Transaction Queue
Create a transaction processing system:
- Define a transaction struct (id, address, data, type)
- Use enum for transaction type (READ, WRITE, MODIFY)
- Store transactions in a queue
- Process transactions in order, updating an associative array "memory"
- Display memory contents after processing

### Exercise 6.2: Scoreboard
Implement a verification scoreboard:
- Use a queue to store expected transactions
- Use associative array for actual received transactions (indexed by id)
- Compare expected vs actual
- Report matches, mismatches, and missing transactions

### Exercise 6.3: Packet Router
Simulate a simple packet router:
- Define packet struct with: dest_addr, priority, data
- Use priority enum
- Store incoming packets in a queue
- Implement routing logic using associative array (address -> port mapping)
- Route packets and display routing decisions

### Exercise 6.4: Memory Manager
Create a memory allocation simulator:
- Use associative array for memory blocks (address -> size)
- Track allocated and free blocks
- Implement allocate(size) function returning address
- Implement free(address) function
- Use structs to represent memory blocks
- Display memory map

### Exercise 6.5: Configuration Database
Implement a simple configuration system:
- Use nested associative arrays (scope -> parameter -> value)
- Support different value types using unions
- Implement set and get functions
- Demonstrate hierarchical parameter storage

### Exercise 6.6: Register Model
Create a register abstraction:
- Define register struct: name, address, fields (using packed struct)
- Store registers in associative array indexed by name
- Implement read/write with field access
- Handle reserved/read-only fields
- Display register contents with field names

---

## 7. Challenge Problems

### Challenge 7.1: Histogram Generator
Create a program that:
- Takes a dynamic array of integer data
- Uses an associative array to count frequency of each value
- Displays a histogram (value -> count)
- Finds mode (most frequent value)
- Handles large sparse datasets efficiently

### Challenge 7.2: LRU Cache
Implement a Least Recently Used cache:
- Fixed size (use parameter)
- Associative array for data storage
- Queue to track access order
- On cache full: evict LRU item
- Track and report hit/miss statistics
- Support get/put operations

### Challenge 7.3: Event Scheduler
Build an event scheduler:
- Events have: time, priority, data
- Use struct for event
- Store in queue, maintain sorted order (earliest first)
- For same time, use priority
- Implement add_event and process_next_event
- Display event processing timeline

### Challenge 7.4: Sparse Matrix
Implement sparse matrix operations:
- Use associative array with 2D index (struct of {row, col})
- Implement matrix addition
- Implement matrix multiplication
- Only store non-zero elements
- Compare memory usage vs regular 2D array

### Challenge 7.5: Graph Representation
Represent and traverse a graph:
- Use associative array: node -> queue of neighbors
- Build a sample graph (5-6 nodes)
- Implement breadth-first search (BFS)
- Use queue for BFS traversal
- Display traversal order

### Challenge 7.6: Compression Dictionary
Create a simple dictionary compression:
- Read sequence of words (strings)
- Build dictionary using associative array (word -> code)
- Assign shorter codes to frequent words
- Encode a sequence of words to codes
- Decode back to verify
- Calculate compression ratio

### Challenge 7.7: Multi-Level Cache Hierarchy
Simulate L1 -> L2 -> Memory hierarchy:
- Three associative arrays (L1, L2, Memory)
- Different sizes and policies
- Implement read with cache propagation
- Track hit rates for each level
- Implement write-through or write-back policy
- Generate statistics report

---

## Testing Guidelines

For each exercise:

1. **Create a testbench** with proper module structure
2. **Use initial blocks** for procedural code
3. **Add displays** to show intermediate results
4. **Test edge cases**: empty structures, full queues, non-existent keys
5. **Comment your code** explaining the concepts being demonstrated
6. **Verify correctness** - think about what outputs you expect

---

## Tips for Success

### Dynamic Arrays
- Always allocate before use: `arr = new[size]`
- Remember size is determined at runtime
- Use when you need resizable but contiguous storage

### Queues  
- Perfect for FIFO/LIFO operations
- Check size before pop operations
- Use bounded queues to prevent unbounded growth

### Associative Arrays
- Great for sparse data structures
- Always check `exists()` before reading
- Use appropriate index type (string for names, int for addresses)

### Structs
- Use `packed` for hardware modeling and bit manipulation
- Use `unpacked` for software-like data structures
- Access fields with dot notation

### Unions
- Remember all fields share storage
- Use tagged unions for type safety
- Useful for viewing data in different formats

### Enums
- Make code self-documenting
- Use in case statements and state machines
- Use `.name()` for debug printing

---

## Common Mistakes to Avoid

1. **Using dynamic array before allocation** → Null pointer error
2. **Popping from empty queue** → Runtime error
3. **Accessing non-existent associative array key** → Returns default value
4. **Forgetting packed on structs when casting to bits** → Won't compile
5. **Shallow copy of dynamic structures** → Both variables point to same data
6. **Not checking randomize() return value** → May miss constraint failures

---

## Sample Solution Structure

```systemverilog
// Example structure for your exercises

module exercise_1_1;
  
  // Declare your data structures here
  int dyn_arr[];
  
  initial begin
    // Your test code here
    
    // 1. Allocate
    dyn_arr = new[10];
    
    // 2. Initialize
    for (int i = 0; i < 10; i++)
      dyn_arr[i] = i;
    
    // 3. Display
    $display("Array size: %0d", dyn_arr.size());
    foreach (dyn_arr[i])
      $display("dyn_arr[%0d] = %0d", i, dyn_arr[i]);
    
    // 4. Cleanup
    dyn_arr.delete();
  end

endmodule
```

---

## Next Steps

After completing these exercises:

1. Move to **classes_oop/** for object-oriented concepts
2. Explore **randomization/** to generate constrained random data
3. Study **interfaces/** for better module connectivity
4. Practice **packages/** for code organization

---

## Resources

- SystemVerilog LRM IEEE 1800-2017
- ChipVerify: https://www.chipverify.com/systemverilog/
- Verification Guide: https://verificationguide.com/systemverilog/

---

**Good luck with your exercises!** Start with the basics and progressively work toward the challenges. Understanding these data types is crucial for effective SystemVerilog design and verification.
