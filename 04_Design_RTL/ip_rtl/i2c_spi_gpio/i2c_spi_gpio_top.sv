`timescale 1ns/1ps

module i2c_spi_gpio_top #
(
    parameter APB_DW = 32,
    parameter APB_AW = 12,
    parameter I2C_CHANNELS = 4,
    parameter SPI_CHANNELS = 4,
    parameter GPIO_WIDTH = 128
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire                    clk_spi,
    input  wire                    rst_spi_n,
    input  wire                    clk_i2c,
    input  wire                    rst_i2c_n,
    input  wire                    clk_gpio,
    input  wire                    rst_gpio_n,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr,

    output wire                    int_global,

    output wire [SPI_CHANNELS-1:0] spi_sck,
    output wire [SPI_CHANNELS-1:0] spi_cs,
    output wire [SPI_CHANNELS-1:0][3:0] spi_mosi,
    input  wire [SPI_CHANNELS-1:0][3:0] spi_miso,

    output wire [I2C_CHANNELS-1:0] i2c_scl,
    inout  wire [I2C_CHANNELS-1:0] i2c_sda,

    input  wire [GPIO_WIDTH-1:0]   gpio_in,
    output wire [GPIO_WIDTH-1:0]   gpio_out,
    output wire [GPIO_WIDTH-1:0]   gpio_oe,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam I2C_OFFSET = 'h000;
    localparam I2C_SIZE   = 'h100;
    localparam SPI_OFFSET = 'h100;
    localparam SPI_SIZE   = 'h100;
    localparam GPIO_OFFSET = 'h200;
    localparam GPIO_SIZE   = 'h100;
    localparam INT_OFFSET  = 'h400;
    localparam INT_SIZE    = 'h100;

    wire [31:0]                   i2c_int_raw [I2C_CHANNELS-1:0];
    wire [31:0]                   spi_int_raw [SPI_CHANNELS-1:0];
    wire [7:0]                    gpio_int_raw;
    wire [31:0]                   int_enable_reg;
    wire [31:0]                   int_raw_reg;
    wire [31:0]                   int_mask_reg;
    wire [31:0]                   int_status_reg;

    genvar                         i;

    generate
        for (i = 0; i < I2C_CHANNELS; i = i + 1) begin : I2C_CH
            i2c_controller_x4 #
            (
                .CHANNEL_ID (i)
            ) u_i2c (
                .clk_apb    (clk_apb),
                .rst_apb_n  (rst_apb_n),
                .clk_i2c    (clk_i2c),
                .rst_i2c_n  (rst_i2c_n),
                .paddr      (paddr),
                .pwrite     (pwrite),
                .pwdata     (pwdata),
                .psel       (psel && (paddr[11:8] == 4'h0)),
                .penable    (penable),
                .prdata     (prdata),
                .pready     (pready),
                .pslverr    (pslverr),
                .i2c_scl    (i2c_scl[i]),
                .i2c_sda    (i2c_sda[i]),
                .int_raw    (i2c_int_raw[i]),
                .test_mode  (test_mode),
                .scan_enable(scan_enable)
            );
        end
    endgenerate

    generate
        for (i = 0; i < SPI_CHANNELS; i = i + 1) begin : SPI_CH
            spi_controller_x4 #
            (
                .CHANNEL_ID (i)
            ) u_spi (
                .clk_apb    (clk_apb),
                .rst_apb_n  (rst_apb_n),
                .clk_spi    (clk_spi),
                .rst_spi_n  (rst_spi_n),
                .paddr      (paddr),
                .pwrite     (pwrite),
                .pwdata     (pwdata),
                .psel       (psel && (paddr[11:8] == 4'h1)),
                .penable    (penable),
                .prdata     (prdata),
                .pready     (pready),
                .pslverr    (pslverr),
                .spi_sck    (spi_sck[i]),
                .spi_cs     (spi_cs[i]),
                .spi_mosi   (spi_mosi[i]),
                .spi_miso   (spi_miso[i]),
                .int_raw    (spi_int_raw[i]),
                .test_mode  (test_mode),
                .scan_enable(scan_enable)
            );
        end
    endgenerate

    gpio_128bit #
    (
        .WIDTH (GPIO_WIDTH)
    ) u_gpio (
        .clk_apb    (clk_apb),
        .rst_apb_n  (rst_apb_n),
        .clk_gpio   (clk_gpio),
        .rst_gpio_n (rst_gpio_n),
        .paddr      (paddr),
        .pwrite     (pwrite),
        .pwdata     (pwdata),
        .psel       (psel && (paddr[11:8] == 4'h2)),
        .penable    (penable),
        .prdata     (prdata),
        .pready     (pready),
        .pslverr    (pslverr),
        .gpio_in    (gpio_in),
        .gpio_out   (gpio_out),
        .gpio_oe    (gpio_oe),
        .int_raw    (gpio_int_raw),
        .test_mode  (test_mode),
        .scan_enable(scan_enable)
    );

    interrupt_aggregator #
    (
        .NUM_SOURCES (I2C_CHANNELS*8 + SPI_CHANNELS*6 + 8)
    ) u_int_agg (
        .clk_apb        (clk_apb),
        .rst_apb_n      (rst_apb_n),
        .int_raw        ({gpio_int_raw, spi_int_raw[3], spi_int_raw[2], spi_int_raw[1], spi_int_raw[0], i2c_int_raw[3], i2c_int_raw[2], i2c_int_raw[1], i2c_int_raw[0]}),
        .int_enable     (int_enable_reg),
        .int_raw_out    (int_raw_reg),
        .int_mask_out   (int_mask_reg),
        .int_status     (int_status_reg),
        .int_global     (int_global),
        .paddr          (paddr),
        .pwrite         (pwrite),
        .pwdata         (pwdata),
        .psel           (psel && (paddr[11:8] == 4'h4)),
        .penable        (penable),
        .prdata         (prdata),
        .pready         (pready),
        .pslverr        (pslverr)
    );

endmodule
