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