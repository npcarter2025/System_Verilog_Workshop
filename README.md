## Directory Structure
```
System_Verilog_Workshop/
├── 01_synthesizable_rtl/
│   ├── basic_cells/
│   ├── fifos/
│   ├── cdc/
│   ├── arbiters/
│   └── fsm/
├── 02_bus_protocols/
│   ├── axi/
│   ├── apb/
│   └── ahb/
├── 03_memory_systems/
├── 04_assertions/
│   ├── immediate/
│   ├── concurrent/
│   └── formal_properties/
├── 05_verification/
│   ├── uvm_basics/
│   ├── constrained_random/
│   ├── coverage/
│   └── scoreboards/
├── 06_advanced_sv_features/
├── 07_dpi_integration/
├── 08_low_power/
├── 09_formal_verification/
└── 10_common_blocks/
```
# Current Tree
```
├── 01_synthesizable_rtl
│   └── README.md
├── 02_bus_protocols
│   └── README.md
├── 03_memory_systems
├── 04_assertions
│   └── README.md
├── 05_verification
│   └── README.md
├── 06_advanced_sv_features
│   ├── README.md
│   └── syntax_practice
├── 07_dpi_integration
├── 08_low_power
│   └── README.md
├── 09_formal_verification
│   └── README.md
├── 10_common_blocks
│   └── README.md
├── README.md
└── systemverilog_oop_practice_tasks.md
```

# Long Term Goal Tree

```
01_synthesizable_rtl/
├── README.md
├── combinational/
│   ├── mux_decoder.sv
│   ├── encoder_priority.sv
│   ├── arithmetic.sv
│   ├── comparators.sv
│   └── README.md
├── sequential/
│   ├── registers.sv
│   ├── counters.sv
│   ├── shift_registers.sv
│   ├── state_machines.sv
│   └── README.md
├── memory/
│   ├── single_port_ram.sv
│   ├── dual_port_ram.sv
│   ├── fifo_sync.sv
│   └── README.md
├── finite_state_machines/
│   ├── moore_fsm.sv
│   ├── mealy_fsm.sv
│   ├── one_hot_fsm.sv
│   ├── gray_fsm.sv
│   └── README.md
├── pipelining/
│   ├── simple_pipeline.sv
│   ├── pipeline_with_stall.sv
│   ├── pipeline_flush.sv
│   └── README.md
└── synthesis_examples/
    ├── resource_sharing.sv
    ├── operator_precedence.sv
    ├── inference_examples.sv
    └── README.md
```
```
02_bus_protocols/
├── system_buses/              # High-performance system interconnects
│   ├── axi/
│   │   ├── axi4_full/
│   │   ├── axi4_lite/
│   │   └── axi4_stream/
│   ├── ahb/
│   ├── apb/
│   ├── wishbone/
│   └── tilelink/              # RISC-V ecosystem
├── serial_buses/              # Serial communication protocols
│   ├── spi/
│   │   ├── spi_master/
│   │   ├── spi_slave/
│   │   └── quad_spi/          # QSPI for flash
│   ├── i2c/
│   │   ├── i2c_master/
│   │   ├── i2c_slave/
│   │   └── multi_master/
│   ├── uart/
│   │   ├── basic_uart/
│   │   └── uart_with_fifo/
│   └── i3c/                   # Improved I2C
├── high_speed_serial/         # High-speed protocols
│   ├── pcie_basics/           # PCIe fundamentals
│   ├── usb/                   # USB protocol basics
│   └── ethernet/              # MAC layer basics
├── memory_interfaces/
│   ├── sram_interface/
│   ├── sdram/
│   ├── ddr_basics/
│   └── flash_spi/
├── streaming/
│   ├── avalon_streaming/
│   └── custom_stream/
└── automotive/                # Automotive protocols
    ├── can/                   # CAN bus
    └── lin/                   # LIN bus

```


```
04_assertions/
├── README.md
├── immediate/
│   ├── basic_immediate.sv
│   ├── error_checking.sv
│   └── README.md
├── concurrent/
│   ├── property_basics.sv
│   ├── sequence_basics.sv
│   ├── implication.sv
│   ├── repetition.sv
│   └── README.md
├── operators/
│   ├── temporal_operators.sv
│   ├── sequence_operators.sv
│   ├── property_operators.sv
│   └── README.md
├── protocol_assertions/
│   ├── handshake_checks.sv
│   ├── valid_ready.sv
│   ├── axi_assertions.sv
│   ├── apb_assertions.sv
│   └── README.md
├── functional_properties/
│   ├── fifo_properties.sv
│   ├── arbiter_properties.sv
│   ├── memory_properties.sv
│   └── README.md
└── coverage_assertions/
    ├── cover_properties.sv
    ├── assertion_coverage.sv
    └── README.md
```

```
05_verification/
├── README.md                          # This file
├── uvm_basics/
│   ├── 01_hello_world/
│   │   ├── hello_uvm.sv
│   │   ├── README.md
│   │   └── run.sh
│   ├── 02_components/
│   │   ├── driver_example.sv
│   │   ├── monitor_example.sv
│   │   ├── sequencer_example.sv
│   │   └── README.md
│   ├── 03_transactions/
│   │   ├── transaction_class.sv
│   │   ├── field_macros_example.sv
│   │   └── README.md
│   ├── 04_sequences/
│   │   ├── base_sequence.sv
│   │   ├── directed_sequence.sv
│   │   ├── random_sequence.sv
│   │   └── README.md
│   ├── 05_agent/
│   │   ├── simple_agent.sv
│   │   ├── active_passive.sv
│   │   ├── config_object.sv
│   │   └── README.md
│   ├── 06_environment/
│   │   ├── env_example.sv
│   │   ├── config_db_usage.sv
│   │   └── README.md
│   ├── 07_test/
│   │   ├── base_test.sv
│   │   ├── test_variations.sv
│   │   └── README.md
│   ├── 08_phases/
│   │   ├── phase_example.sv
│   │   └── README.md
│   └── README.md
├── uvm_intermediate/
│   ├── 01_virtual_sequences/
│   │   ├── virtual_sequencer.sv
│   │   ├── multi_interface_seq.sv
│   │   └── README.md
│   ├── 02_callbacks/
│   │   ├── driver_callbacks.sv
│   │   ├── test_callbacks.sv
│   │   └── README.md
│   ├── 03_factory/
│   │   ├── factory_override.sv
│   │   ├── type_override.sv
│   │   ├── instance_override.sv
│   │   └── README.md
│   ├── 04_objections/
│   │   ├── test_objections.sv
│   │   ├── phase_objections.sv
│   │   └── README.md
│   ├── 05_reporting/
│   │   ├── custom_reporter.sv
│   │   ├── report_server.sv
│   │   └── README.md
│   ├── 06_tlm/
│   │   ├── tlm_ports.sv
│   │   ├── tlm_analysis_port.sv
│   │   ├── tlm_fifos.sv
│   │   └── README.md
│   └── README.md
├── uvm_advanced/
│   ├── 01_ral/                        # Register Abstraction Layer
│   │   ├── simple_reg_model/
│   │   │   ├── my_reg_block.sv
│   │   │   ├── reg_adapter.sv
│   │   │   ├── reg_predictor.sv
│   │   │   └── README.md
│   │   ├── reg_sequences/
│   │   │   ├── reg_single_access.sv
│   │   │   ├── reg_bit_bash.sv
│   │   │   ├── reg_mem_walk.sv
│   │   │   └── README.md
│   │   └── README.md
│   ├── 02_coverage_driven/
│   │   ├── coverage_collector.sv
│   │   ├── coverage_driven_test.sv
│   │   └── README.md
│   ├── 03_phasing_advanced/
│   │   ├── phase_jumping.sv
│   │   ├── custom_phases.sv
│   │   └── README.md
│   ├── 04_configuration_advanced/
│   │   ├── resource_db.sv
│   │   ├── config_patterns.sv
│   │   └── README.md
│   └── README.md
├── constrained_random/
│   ├── basic_constraints/
│   │   ├── simple_constraints.sv
│   │   ├── dist_constraints.sv       # Distribution weights
│   │   ├── implication.sv            # -> operator
│   │   ├── array_constraints.sv
│   │   └── README.md
│   ├── advanced_constraints/
│   │   ├── soft_constraints.sv
│   │   ├── solve_before.sv
│   │   ├── dynamic_constraints.sv    # constraint_mode
│   │   ├── inline_constraints.sv     # randomize() with {}
│   │   ├── pre_post_randomize.sv
│   │   └── README.md
│   ├── constraint_patterns/
│   │   ├── address_alignment.sv
│   │   ├── protocol_constraints.sv
│   │   ├── performance_constraints.sv
│   │   ├── exclusion_constraints.sv
│   │   └── README.md
│   └── README.md
├── functional_coverage/
│   ├── basic_coverage/
│   │   ├── covergroup_basics.sv
│   │   ├── coverpoint.sv
│   │   ├── bins_example.sv
│   │   └── README.md
│   ├── advanced_coverage/
│   │   ├── cross_coverage.sv
│   │   ├── transition_bins.sv
│   │   ├── illegal_bins.sv
│   │   ├── ignore_bins.sv
│   │   ├── per_instance_coverage.sv
│   │   └── README.md
│   ├── coverage_driven/
│   │   ├── coverage_feedback.sv
│   │   └── README.md
│   └── README.md
├── scoreboards/
│   ├── basic_scoreboard/
│   │   ├── fifo_scoreboard.sv        # In-order checking
│   │   └── README.md
│   ├── reorder_scoreboard/
│   │   ├── associative_array_sb.sv   # Out-of-order checking
│   │   └── README.md
│   ├── predictor/
│   │   ├── reference_model.sv
│   │   ├── predictor_scoreboard.sv
│   │   └── README.md
│   └── README.md
├── verification_ips/                  # Reusable VIPs
│   ├── apb_vip/
│   │   ├── apb_transaction.sv
│   │   ├── apb_driver.sv
│   │   ├── apb_monitor.sv
│   │   ├── apb_sequencer.sv
│   │   ├── apb_agent.sv
│   │   ├── apb_config.sv
│   │   ├── sequences/
│   │   │   ├── apb_base_seq.sv
│   │   │   ├── apb_write_seq.sv
│   │   │   ├── apb_read_seq.sv
│   │   │   └── apb_random_seq.sv
│   │   └── README.md
│   ├── axi_lite_vip/
│   │   └── ... (similar structure)
│   ├── uart_vip/
│   │   └── ...
│   └── README.md
├── testbench_patterns/
│   ├── layered_testbench/
│   │   └── README.md
│   ├── interface_based/
│   │   ├── interface_example.sv
│   │   ├── modport_usage.sv
│   │   └── README.md
│   ├── clocking_blocks/
│   │   ├── clocking_example.sv
│   │   └── README.md
│   └── README.md
├── debug_techniques/
│   ├── waveform_dump.sv
│   ├── transaction_recording.sv
│   ├── uvm_debug_messaging.sv
│   └── README.md
├── non_uvm_verification/              # Other methodologies
│   ├── basic_testbench/
│   │   ├── simple_tb.sv
│   │   └── README.md
│   ├── class_based_tb/
│   │   ├── mailbox_example.sv
│   │   ├── semaphore_example.sv
│   │   ├── event_example.sv
│   │   └── README.md
│   └── README.md
└── complete_examples/                 # Full working examples
    ├── simple_alu_uvm/
    │   ├── dut/
    │   │   └── alu.sv
    │   ├── tb/
    │   │   ├── alu_if.sv
    │   │   ├── alu_transaction.sv
    │   │   ├── alu_sequence.sv
    │   │   ├── alu_driver.sv
    │   │   ├── alu_monitor.sv
    │   │   ├── alu_agent.sv
    │   │   ├── alu_scoreboard.sv
    │   │   ├── alu_env.sv
    │   │   └── alu_test.sv
    │   ├── sim/
    │   │   ├── run.sh
    │   │   └── Makefile
    │   └── README.md
    ├── fifo_uvm/
    │   └── ...
    └── uart_uvm/
        └── ...
```



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

```
08_low_power/
├── README.md                        # This file
├── clock_gating/
│   ├── integrated_clock_gating/
│   │   ├── icg_cell.sv              # Latch-based clock gate
│   │   ├── icg_safe.sv              # Glitch-free implementation
│   │   ├── icg_tb.sv                # Testbench
│   │   └── README.md
│   ├── rtl_clock_gating/
│   │   ├── auto_gated_reg.sv        # Register with enable gating
│   │   ├── conditional_gating.sv    # Gate based on logic conditions
│   │   ├── pipeline_gating.sv       # Gate pipeline stages
│   │   └── README.md
│   └── clock_gating_assertions.sv   # SVA to verify no glitches
├── power_domains/
│   ├── isolation_cells/
│   │   ├── iso_cell_high.sv         # Clamp to high when off
│   │   ├── iso_cell_low.sv          # Clamp to low when off
│   │   ├── iso_cell_latch.sv        # Latch last value
│   │   └── README.md
│   ├── level_shifters/
│   │   ├── level_shifter_up.sv      # Low to high voltage
│   │   ├── level_shifter_down.sv    # High to low voltage
│   │   └── README.md
│   └── power_switches/
│       ├── header_switch.sv         # PMOS power switch
│       ├── footer_switch.sv         # NMOS ground switch
│       └── README.md
├── retention/
│   ├── retention_register.sv        # Retains value in sleep mode
│   ├── retention_fifo.sv            # FIFO with retention
│   ├── save_restore_fsm.sv          # State save/restore logic
│   └── README.md
├── dvfs/                            # Dynamic Voltage/Frequency Scaling
│   ├── freq_divider_dynamic.sv      # Runtime frequency adjustment
│   ├── voltage_monitor.sv           # Simple voltage detector
│   ├── performance_counter.sv       # Track activity for DVFS
│   └── README.md
├── power_aware_design/
│   ├── operand_isolation.sv         # Prevent toggling unused logic
│   ├── memory_power_down.sv         # RAM sleep modes
│   ├── multi_vt_example.sv          # High-Vt and Low-Vt usage notes
│   ├── gated_compute_unit.sv        # Power gate entire block
│   └── README.md
├── upf_examples/                    # Unified Power Format
│   ├── simple_power_domain.upf      # Basic UPF commands
│   ├── multi_domain.upf             # Multiple power domains
│   ├── isolation_strategy.upf       # Isolation cells specification
│   ├── retention_strategy.upf       # Retention specification
│   └── README.md
└── verification/
    ├── power_aware_tb.sv            # Testbench for power modes
    ├── power_state_monitor.sv       # Check legal power states
    ├── retention_checker.sv         # Verify data retention
    └── README.md
```


```
09_formal_verification/
├── README.md                        # This file
├── basic_properties/
│   ├── safety_properties.sv         # "Bad thing never happens"
│   ├── liveness_properties.sv       # "Good thing eventually happens"
│   ├── fairness_properties.sv       # Fair arbitration
│   └── README.md
├── protocol_compliance/
│   ├── axi_formal_properties.sv     # AXI protocol checks
│   ├── apb_formal_properties.sv     # APB protocol checks
│   ├── handshake_formal.sv          # Valid-ready handshake
│   ├── i2c_formal_properties.sv     # I2C start/stop conditions
│   └── README.md
├── data_integrity/
│   ├── fifo_formal_proof.sv         # Prove FIFO correctness
│   ├── counter_formal.sv            # Prove counter bounds
│   ├── memory_formal.sv             # Memory read/write consistency
│   └── README.md
├── bounded_proofs/
│   ├── mutex_proof.sv               # Mutual exclusion proof
│   ├── arbiter_proof.sv             # Fair arbitration proof
│   ├── deadlock_freedom.sv          # Prove no deadlock
│   └── README.md
├── cover_properties/
│   ├── reachability.sv              # Prove state is reachable
│   ├── corner_cases.sv              # Reach interesting scenarios
│   ├── protocol_sequences.sv        # Valid transaction sequences
│   └── README.md
├── assume_guarantee/
│   ├── environment_assumptions.sv   # Assume valid inputs
│   ├── interface_contracts.sv       # Module contracts
│   ├── compositional_proof.sv       # Proof composition
│   └── README.md
├── equivalence/
│   ├── sequential_equivalence.sv    # Before/after optimization
│   ├── fsm_equivalence.sv           # Different FSM encodings
│   ├── pipeline_equivalence.sv      # Pipelined vs non-pipelined
│   └── README.md
└── case_studies/
    ├── cdc_formal/                  # CDC correctness
    │   ├── gray_code_proof.sv       # Prove gray code properties
    │   ├── handshake_sync_proof.sv  # 2-FF synchronizer + handshake
    │   ├── mcp_proof.sv             # Multi-cycle path
    │   └── README.md
    ├── fifo_full_proof/
    │   ├── fifo_model.sv
    │   ├── fifo_properties.sv
    │   ├── formal_tb.sv
    │   └── README.md
    └── arbiter_fairness/
        ├── rr_arbiter.sv
        ├── fairness_proof.sv
        └── README.md
```


```
10_common_blocks/
├── README.md                          # This file
├── arbiters/
│   ├── fixed_priority_arbiter.sv
│   ├── round_robin_arbiter.sv
│   ├── weighted_round_robin.sv
│   ├── matrix_arbiter.sv              # Fully parallel
│   ├── arbiter_tb.sv
│   └── README.md
├── fifos/
│   ├── sync_fifo.sv                   # Single clock domain
│   ├── async_fifo.sv                  # Dual clock domain (gray code)
│   ├── showahead_fifo.sv              # Data appears immediately
│   ├── fwft_fifo.sv                   # First-Word-Fall-Through
│   ├── skid_buffer.sv                 # Pipeline register with backpressure
│   ├── fifo_tb.sv
│   └── README.md
├── synchronizers/
│   ├── two_flop_sync.sv               # Basic bit synchronizer
│   ├── handshake_sync.sv              # Req-ack synchronizer
│   ├── pulse_sync.sv                  # Pulse synchronizer
│   ├── mcp_fifo.sv                    # Multi-bit synchronizer
│   ├── reset_sync.sv                  # Reset synchronizer
│   └── README.md
├── counters/
│   ├── binary_counter.sv
│   ├── gray_counter.sv                # For async boundaries
│   ├── johnson_counter.sv
│   ├── lfsr.sv                        # Linear Feedback Shift Register
│   ├── one_hot_counter.sv
│   ├── modulo_counter.sv
│   └── README.md
├── muxes_decoders/
│   ├── parameterized_mux.sv
│   ├── one_hot_mux.sv
│   ├── binary_decoder.sv
│   ├── priority_encoder.sv
│   ├── one_hot_to_binary.sv
│   ├── thermometer_encoder.sv
│   └── README.md
├── error_detection/
│   ├── parity_generator.sv            # Even/odd parity
│   ├── crc_calculator.sv              # CRC-8, CRC-16, CRC-32
│   ├── hamming_encoder.sv             # Single-error correction
│   ├── hamming_decoder.sv             # SECDED
│   └── README.md
├── shifters/
│   ├── barrel_shifter.sv              # Combinational shifter
│   ├── serial_to_parallel.sv          # Deserializer
│   ├── parallel_to_serial.sv          # Serializer
│   ├── lfsr_scrambler.sv              # Data scrambling
│   └── README.md
├── edge_detectors/
│   ├── rising_edge_detect.sv
│   ├── falling_edge_detect.sv
│   ├── any_edge_detect.sv
│   ├── pulse_generator.sv
│   ├── pulse_stretcher.sv
│   └── README.md
├── delay_elements/
│   ├── fixed_delay.sv
│   ├── programmable_delay.sv
│   └── README.md
├── rate_adaptation/
│   ├── clock_divider.sv               # Integer division
│   ├── fractional_divider.sv
│   ├── rate_matcher.sv                # Elastic buffer
│   ├── gearbox.sv                     # Width + rate conversion
│   └── README.md
├── width_converters/
│   ├── upsizer.sv                     # Narrow to wide
│   ├── downsizer.sv                   # Wide to narrow
│   ├── axis_width_converter.sv        # AXI-Stream based
│   └── README.md
└── utility/
    ├── debouncer.sv                   # Button debouncing
    ├── timeout_counter.sv
    ├── watchdog_timer.sv
    ├── pulse_extender.sv
    ├── onehot_checker.sv
    └── README.md
```
