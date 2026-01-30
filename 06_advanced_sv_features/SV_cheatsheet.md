# SystemVerilog Debugging & Data Structures Cheat Sheet

This quick reference covers queue operations, display formatting, and timing helpers for clear simulation output.

---

## 1. Queues (`[$]`)

Queues are flexible, ordered collections that grow and shrink dynamically—perfect for FIFOs, stacks, and scoreboards.

### Declaration & Initialization

```systemverilog
int my_queue [$];               // Unbounded queue of integers
int bounded_q [$:49];           // Bounded: max 50 elements (0 to 49)
int init_q [$] = {1, 2, 3};     // Initialized queue
```

### Common Queue Methods

| Method | Description |
|--------|-------------|
| `size()` | Returns the number of items in the queue |
| `push_back(val)` | Appends `val` to the end |
| `push_front(val)` | Inserts `val` at the front |
| `pop_back()` | Removes and returns the last element |
| `pop_front()` | Removes and returns the first element |
| `insert(idx, val)` | Inserts `val` at index `idx` |
| `delete(idx)` | Deletes the item at index `idx`; omit index to clear queue |

### Tips
- Use `foreach (queue[i])` to iterate in order
- Guard `pop_*()` with `size()` checks to avoid runtime errors
- Use bounded queues (`[$:N]`) for hardware FIFO modeling

---

## 2. Display Tasks

| Task | Execution Region | Behavior |
|------|------------------|----------|
| `$display` | Active | Prints immediately; adds a newline |
| `$write` | Active | Prints immediately; no automatic newline |
| `$strobe` | Postponed | Prints at the end of the timestep (captures settled values) |
| `$monitor` | Postponed | Automatically prints whenever any argument changes |

---

## 3. Format Specifiers

| Specifier | Format | Pro Tip |
|-----------|--------|---------|
| `%d` | Decimal | Use `%0d` to suppress leading spaces |
| `%h` | Hexadecimal | Use `%0h` for clean hex output |
| `%b` | Binary | Shows `x` and `z` states |
| `%s` | String | Interprets bytes as ASCII characters |
| `%t` | Time | Respects settings from `$timeformat` |
| `%p` | Pattern | **Power user:** Prints entire arrays, queues, or structs |
| `%m` | Module | Prints the full hierarchical path of the module |

---

## 4. Special System Functions

### `$sformatf`

Returns a formatted string without printing to console. Perfect for creating dynamic strings for UVM reporting or error messages.

```systemverilog
string s;
s = $sformatf("Value is: %0h", 8'hA5);
```

### `$timeformat`

Sets the global format for the `%t` specifier.

**Syntax:** `$timeformat(unit, precision, suffix, min_width);`

**Units:** `-9` (ns), `-12` (ps), `-15` (fs)

```systemverilog
initial begin
    $timeformat(-9, 2, " ns", 10);
    $display("Time is %t", $time); // Outputs: "     0.00 ns"
end
```

### `$monitoron` / `$monitoroff`

Used to enable or disable the `$monitor` task during specific parts of the simulation to reduce log noise.

---

## 5. Practical Summary Example

```systemverilog
module test;
    int data_q [$];

    initial begin
        $timeformat(-9, 0, "ns");
        $monitor("%t | Queue updated. Size: %0d", $time, data_q.size());

        #10 data_q.push_back(5);
        #10 data_q.push_back(10);
        
        $strobe("Final state: %p", data_q); // Prints '{5, 10} at end of time 20
        $finish;
    end
endmodule
```

---

## Quick Tips

- **Consistent formatting:** Use `%0d`, `%0h`, `%p` consistently for easy log parsing
- **Stable values:** Use `$strobe` to capture final values after all blocking assignments
- **Reduce noise:** Toggle `$monitor` with `$monitoron`/`$monitoroff` around sections you need to trace
- **Queue safety:** Always check `size()` before popping to avoid runtime errors
- **Debug arrays:** Use `%p` to print entire data structures in one go
