`timescale 1ns/1ps

module can_error_handler #
(
    parameter TX_ERR_LIMIT = 255,
    parameter RX_ERR_LIMIT = 255
)
(
    input  wire                    clk_can,
    input  wire                    rst_n,
    input  wire                    can_rx,
    input  wire                    tx_done,
    input  wire                    rx_ready,
    output reg                     crc_error,
    output reg                     form_error,
    output reg                     bit_error,
    output reg                     ack_error,
    output reg  [7:0]              err_tx_count,
    output reg  [7:0]              err_rx_count,
    output reg                     error_warning,
    output reg                     error_passive,
    output reg                     bus_off,
    output reg                     active_err
);

    localparam TX_WARN_LIMIT = 96;
    localparam RX_WARN_LIMIT = 96;
    localparam TX_PASS_LIMIT = 127;
    localparam RX_PASS_LIMIT = 127;

    reg                            tx_error_flag;
    reg                            rx_error_flag;
    reg                            error_active;
    reg                            error_passive_state;
    reg                            bus_off_state;
    reg  [5:0]                     error_counter;
    reg                            start_error_flag;
    reg                            suspend_transmission;
    reg  [7:0]                     recovery_counter;

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            err_tx_count <= '0;
            err_rx_count <= '0;
            error_warning <= 1'b0;
            error_passive <= 1'b0;
            bus_off <= 1'b0;
            active_err <= 1'b0;
            error_passive_state <= 1'b0;
            bus_off_state <= 1'b0;
        end else begin
            if (tx_done && tx_error_flag) begin
                if (err_tx_count < TX_ERR_LIMIT) begin
                    err_tx_count <= err_tx_count + 1;
                end
                tx_error_flag <= 1'b0;
            end

            if (rx_ready && rx_error_flag) begin
                if (err_rx_count < RX_ERR_LIMIT) begin
                    err_rx_count <= err_rx_count + 1;
                end
                rx_error_flag <= 1'b0;
            end

            if (err_tx_count >= TX_WARN_LIMIT || err_rx_count >= RX_WARN_LIMIT) begin
                error_warning <= 1'b1;
            end else begin
                error_warning <= 1'b0;
            end

            if (err_tx_count >= TX_PASS_LIMIT || err_rx_count >= RX_PASS_LIMIT) begin
                error_passive <= 1'b1;
                error_passive_state <= 1'b1;
            end else if (err_tx_count < TX_PASS_LIMIT && err_rx_count < RX_PASS_LIMIT) begin
                if (error_passive_state) begin
                    error_passive <= 1'b0;
                    error_passive_state <= 1'b0;
                end
            end

            if (err_tx_count >= TX_ERR_LIMIT) begin
                bus_off <= 1'b1;
                bus_off_state <= 1'b1;
                active_err <= 1'b0;
            end

            if (bus_off_state && recovery_counter >= 128) begin
                if (can_rx == 1'b1) begin
                    bus_off <= 1'b0;
                    bus_off_state <= 1'b0;
                    err_tx_count <= '0;
                    err_rx_count <= '0;
                    error_warning <= 1'b0;
                    error_passive <= 1'b0;
                end
            end

            if (tx_done && !tx_error_flag && !bus_off_state) begin
                if (err_tx_count > 0) begin
                    err_tx_count <= err_tx_count - 1;
                end
            end

            if (rx_ready && !rx_error_flag && !bus_off_state) begin
                if (err_rx_count > 0) begin
                    err_rx_count <= err_rx_count - 1;
                end
            end
        end
    end

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            error_active <= 1'b0;
            active_err <= 1'b0;
            start_error_flag <= 1'b0;
            error_counter <= '0;
            suspend_transmission <= 1'b0;
            recovery_counter <= '0;
        end else begin
            if (bus_off_state) begin
                recovery_counter <= recovery_counter + 1;
            end else begin
                recovery_counter <= '0;
            end

            if (crc_error || form_error || bit_error || ack_error) begin
                start_error_flag <= 1'b1;
            end

            if (start_error_flag) begin
                if (error_counter < 31) begin
                    error_counter <= error_counter + 1;
                    error_active <= 1'b1;
                    active_err <= 1'b1;
                end else begin
                    if (error_passive_state) begin
                        if (error_counter < 127) begin
                            error_counter <= error_counter + 1;
                            error_active <= 1'b1;
                        end else begin
                            start_error_flag <= 1'b0;
                            error_active <= 1'b0;
                            active_err <= 1'b0;
                        end
                    end else begin
                        start_error_flag <= 1'b0;
                        error_active <= 1'b0;
                        active_err <= 1'b0;
                    end
                end

                tx_error_flag <= 1'b1;
                rx_error_flag <= 1'b1;
            end else begin
                if (error_counter > 0) begin
                    if (error_counter < 8) begin
                        error_counter <= '0;
                        error_active <= 1'b0;
                    end else begin
                        error_counter <= error_counter - 1;
                    end
                end
            end
        end
    end

endmodule
