#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "esp_system.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "driver/gpio.h"
#include "driver/uart.h"
#include "driver/i2c_master.h"
#include "led_strip.h"

#define TAG "ESP32_P4_MAIN"
#define MY_RAIL_SEQ          1

#define RPI_UART_NUM         UART_NUM_1
#define RPI_TX_PIN           48
#define RPI_RX_PIN           47

#define WROOM_CTRL_UART_NUM  UART_NUM_2
#define WROOM_CTRL_TX_PIN    53
#define WROOM_CTRL_RX_PIN    54

#define UART_BUF_SIZE        1024

#define RELAY_PIN            GPIO_NUM_2
#define PROJECTOR_PIN        GPIO_NUM_11

#define DATA_PIN_1           GPIO_NUM_4
#define DATA_PIN_2           GPIO_NUM_5
#define NUM_ROWS             4
#define LEDS_PER_ROW         31
#define NUM_LEDS             (LEDS_PER_ROW * NUM_ROWS)

#define I2C_SDA_PIN          GPIO_NUM_8
#define I2C_SCL_PIN          GPIO_NUM_9
#define I2C_FREQ_HZ          400000
#define INA219_ADDR_LEFT     0x40
#define INA219_ADDR_RIGHT    0x41

#pragma pack(push, 1)
typedef struct {
    uint8_t  header1;
    uint8_t  header2;
    uint16_t in_count;
    uint16_t out_count;
    int16_t  r1_x[3];
    int16_t  r1_y[3];
    int16_t  r2_x[3];
    int16_t  r2_y[3];
    uint8_t  r1_detected;
    uint8_t  r2_detected;
    uint8_t  emergency_code;
    uint8_t  checksum;
} radar_rx_frame_t;
#pragma pack(pop)

static radar_rx_frame_t s_rx_radar_data = {0};
static SemaphoreHandle_t s_state_mutex = NULL;
static SemaphoreHandle_t s_wroom_tx_mutex = NULL;
static SemaphoreHandle_t s_rpi_tx_mutex = NULL;

static led_strip_handle_t s_strip1 = NULL;
static led_strip_handle_t s_strip2 = NULL;

static i2c_master_bus_handle_t s_i2c_bus_handle = NULL;
static i2c_master_dev_handle_t s_ina_dev_left = NULL;
static i2c_master_dev_handle_t s_ina_dev_right = NULL;

static volatile uint8_t  s_power_supply_mode = 0;
static volatile bool     s_is_sleep_mode     = false;
static volatile bool     s_is_projector_on   = true;

static volatile uint8_t  s_current_category  = 0;
static volatile uint8_t  s_current_sub_mode  = 1;
static volatile uint8_t  s_music_led_pattern = 0;

static volatile bool     s_is_music_on       = false;
static volatile int      s_current_volume    = 20;
static volatile int      s_play_mode         = 0;
static volatile int      s_target_track      = 1;
static volatile bool     s_voice_call_mode   = false;

static volatile uint8_t  s_latest_bat_pct    = 0;
static volatile uint16_t s_latest_l_mw       = 0;
static volatile uint16_t s_latest_r_mw       = 0;
static uint32_t          s_anim_frame        = 0;

static volatile int64_t  s_sleep_wake_timer  = 0;
#define HOLD_TIME_MS     10000

static volatile bool     s_system_power_state = true;
static bool              s_last_power_state   = true;

static uint8_t s_audio_bands[8] = {0};
static bool s_is_left_ina_ready = false;
static bool s_is_right_ina_ready = false;

static uint8_t s_fb1[NUM_LEDS][3] = {0};
static uint8_t s_fb2[NUM_LEDS][3] = {0};

static inline int64_t millis(void) {
    return esp_timer_get_time() / 1000;
}

static uint8_t sine8(uint8_t theta) {
    float rad = (float)theta * (2.0f * (float)M_PI / 256.0f);
    float val = (sinf(rad) + 1.0f) * 127.5f;
    return (uint8_t)(val > 255.0f ? 255 : (val < 0.0f ? 0 : val));
}

static void set_pixel1(uint8_t row, uint8_t col, uint8_t r, uint8_t g, uint8_t b) {
    if (row >= NUM_ROWS || col >= LEDS_PER_ROW) return;
    if (row % 2 == 1) col = (LEDS_PER_ROW - 1) - col;
    uint16_t idx = (row * LEDS_PER_ROW) + col;
    if (idx < NUM_LEDS) { s_fb1[idx][0] = r; s_fb1[idx][1] = g; s_fb1[idx][2] = b; }
}

static void set_pixel2(uint8_t row, uint8_t col, uint8_t r, uint8_t g, uint8_t b) {
    if (row >= NUM_ROWS || col >= LEDS_PER_ROW) return;
    if (row % 2 == 1) col = (LEDS_PER_ROW - 1) - col;
    uint16_t idx = (row * LEDS_PER_ROW) + col;
    if (idx < NUM_LEDS) { s_fb2[idx][0] = r; s_fb2[idx][1] = g; s_fb2[idx][2] = b; }
}

static void clear_all_leds(void) {
    memset(s_fb1, 0, sizeof(s_fb1));
    memset(s_fb2, 0, sizeof(s_fb2));
}

static void flush_led_strips(void) {
    for (int i = 0; i < NUM_LEDS; i++) {
        led_strip_set_pixel(s_strip1, i, s_fb1[i][0], s_fb1[i][1], s_fb1[i][2]);
        led_strip_set_pixel(s_strip2, i, s_fb2[i][0], s_fb2[i][1], s_fb2[i][2]);
    }
    led_strip_refresh(s_strip1);
    led_strip_refresh(s_strip2);
}

static void update_led_sequence(void) {
    int64_t current_millis = millis();
    static int64_t last_led_update = 0;

    if (s_voice_call_mode) {
        if (current_millis - last_led_update > 30) {
            last_led_update = current_millis;
            uint8_t breathe = sine8(s_anim_frame * 3);
            uint8_t r_val = (breathe > 60) ? (breathe - 60) : 0;
            for (int i = 0; i < NUM_LEDS; i++) {
                s_fb1[i][0] = r_val; s_fb1[i][1] = r_val / 4; s_fb1[i][2] = 0;
                s_fb2[i][0] = r_val; s_fb2[i][1] = r_val / 4; s_fb2[i][2] = 0;
            }
            s_anim_frame++;
            flush_led_strips();
        }
        return;
    }

    if (current_millis - last_led_update > 20) {
        last_led_update = current_millis;
        for (uint8_t r = 0; r < NUM_ROWS; r++) {
            for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                uint8_t bright = sine8((c * 12) + (r * 40) + (s_anim_frame * 4));
                set_pixel1(r, c, bright / 4, 0, bright);
                set_pixel2(r, c, 0, bright / 4, bright);
            }
        }
        s_anim_frame++;
        flush_led_strips();
    }
}

static esp_err_t ina219_read_reg(i2c_master_dev_handle_t dev_handle, uint8_t reg, uint16_t *val) {
    if (!dev_handle) return ESP_FAIL;
    uint8_t buf[2];
    esp_err_t ret = i2c_master_transmit_receive(dev_handle, &reg, 1, buf, 2, pdMS_TO_TICKS(50));
    if (ret == ESP_OK) *val = (buf[0] << 8) | buf[1];
    return ret;
}

static esp_err_t init_ina219_dev(i2c_master_dev_handle_t dev_handle) {
    if (!dev_handle) return ESP_FAIL;
    uint8_t config[3] = {0x00, 0x39, 0x9F};
    esp_err_t ret = i2c_master_transmit(dev_handle, config, 3, pdMS_TO_TICKS(50));
    if (ret == ESP_OK) {
        uint8_t cal[3] = {0x05, 0x10, 0x00};
        ret = i2c_master_transmit(dev_handle, cal, 3, pdMS_TO_TICKS(50));
    }
    return ret;
}

static void read_battery_and_calculate_pct(void) {
    uint16_t l_raw_v = 0, r_raw_v = 0, l_raw_p = 0, r_raw_p = 0;
    if (s_is_left_ina_ready) {
        ina219_read_reg(s_ina_dev_left, 0x02, &l_raw_v);
        ina219_read_reg(s_ina_dev_left, 0x03, &l_raw_p);
    }
    if (s_is_right_ina_ready) {
        ina219_read_reg(s_ina_dev_right, 0x02, &r_raw_v);
        ina219_read_reg(s_ina_dev_right, 0x03, &r_raw_p);
    }

    s_latest_l_mw = l_raw_p * 20;
    s_latest_r_mw = r_raw_p * 20;

    float l_volt = (l_raw_v >> 3) * 0.004f;
    float r_volt = (r_raw_v >> 3) * 0.004f;
    float raw_avg_v = (l_volt > 0.1f) ? l_volt : r_volt;

    float max_watt = (s_latest_l_mw > s_latest_r_mw ? s_latest_l_mw : s_latest_r_mw) / 1000.0f;
    float comp_v = raw_avg_v - (max_watt * 0.015f);
    if (comp_v < 10.8f) comp_v = 10.8f;

    long mapped = (long)((comp_v * 100.0f - 1080.0f) * 100.0f / (1360.0f - 1080.0f));
    if (mapped < 0) mapped = 0;
    if (mapped > 100) mapped = 100;
    s_latest_bat_pct = (uint8_t)mapped;
}

static void send_to_wroom(const char *cmd) {
    if (s_wroom_tx_mutex && xSemaphoreTake(s_wroom_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        uart_write_bytes(WROOM_CTRL_UART_NUM, cmd, strlen(cmd));
        xSemaphoreGive(s_wroom_tx_mutex);
    }
}

static void send_bytes_to_rpi(const void *data, size_t len) {
    if (s_rpi_tx_mutex && xSemaphoreTake(s_rpi_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        uart_write_bytes(RPI_UART_NUM, (const char *)data, len);
        xSemaphoreGive(s_rpi_tx_mutex);
    }
}

typedef enum { FSM_IDLE, FSM_FIND_55, FSM_READ_BODY, FSM_FIND_5A, FSM_READ_VOICE_LEN, FSM_READ_VOICE_BODY, FSM_READ_TEXT } unified_fsm_t;

static void handle_wroom_stream_rx(void) {
    static unified_fsm_t s_fsm_state = FSM_IDLE;
    static uint8_t s_rx_buf[34];
    static int s_body_idx = 0;
    static uint8_t s_voice_buf[64];
    static int s_voice_len = 0;
    static int s_voice_idx = 0;
    static char s_txt_buf[128];
    static int s_txt_idx = 0;

    uint8_t temp[128];
    int len = uart_read_bytes(WROOM_CTRL_UART_NUM, temp, sizeof(temp), 0);

    if (len > 0) {
        for (int i = 0; i < len; i++) {
            uint8_t b = temp[i];

            switch (s_fsm_state) {
            case FSM_IDLE:
                if (b == 0xAA) { s_rx_buf[0] = 0xAA; s_fsm_state = FSM_FIND_55; }
                else if (b == 0xA5) { s_fsm_state = FSM_FIND_5A; }
                else if (b == '$') { s_txt_idx = 0; s_txt_buf[s_txt_idx++] = (char)b; s_fsm_state = FSM_READ_TEXT; }
                break;

            case FSM_FIND_55:
                if (b == 0x55) { s_rx_buf[1] = 0x55; s_body_idx = 2; s_fsm_state = FSM_READ_BODY; }
                else { s_fsm_state = FSM_IDLE; }
                break;

            case FSM_READ_BODY:
                s_rx_buf[s_body_idx++] = b;
                if (s_body_idx >= 34) {
                    uint8_t chk = 0;
                    for (int j = 2; j < 33; j++) chk ^= s_rx_buf[j];

                    if (chk == s_rx_buf[33]) {
                        radar_rx_frame_t temp_pkt;
                        temp_pkt.header1 = 0xAA; temp_pkt.header2 = 0x55;
                        temp_pkt.in_count  = (s_rx_buf[2] << 8) | s_rx_buf[3];
                        temp_pkt.out_count = (s_rx_buf[4] << 8) | s_rx_buf[5];
                        for (int k = 0; k < 3; k++) {
                            temp_pkt.r1_x[k] = (int16_t)((s_rx_buf[6 + (k * 2)] << 8) | s_rx_buf[7 + (k * 2)]);
                            temp_pkt.r1_y[k] = (int16_t)((s_rx_buf[12 + (k * 2)] << 8) | s_rx_buf[13 + (k * 2)]);
                            temp_pkt.r2_x[k] = (int16_t)((s_rx_buf[18 + (k * 2)] << 8) | s_rx_buf[19 + (k * 2)]);
                            temp_pkt.r2_y[k] = (int16_t)((s_rx_buf[24 + (k * 2)] << 8) | s_rx_buf[25 + (k * 2)]);
                        }
                        temp_pkt.r1_detected = s_rx_buf[30];
                        temp_pkt.r2_detected = s_rx_buf[31];
                        temp_pkt.emergency_code = s_rx_buf[32];
                        temp_pkt.checksum = s_rx_buf[33];

                        if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                            s_rx_radar_data = temp_pkt;
                            xSemaphoreGive(s_state_mutex);
                        }
                    }
                    s_fsm_state = FSM_IDLE;
                    s_body_idx = 0;
                }
                break;

            case FSM_FIND_5A:
                s_fsm_state = (b == 0x5A) ? FSM_READ_VOICE_LEN : FSM_IDLE;
                break;

            case FSM_READ_VOICE_LEN:
                s_voice_len = b;
                s_voice_idx = 0;
                if (s_voice_len > 0 && s_voice_len <= 60) {
                    s_voice_buf[0] = 0xA5; s_voice_buf[1] = 0x5A; s_voice_buf[2] = (uint8_t)s_voice_len;
                    s_fsm_state = FSM_READ_VOICE_BODY;
                } else {
                    s_fsm_state = FSM_IDLE;
                }
                break;

            case FSM_READ_VOICE_BODY:
                s_voice_buf[3 + s_voice_idx++] = b;
                if (s_voice_idx >= s_voice_len) {
                    send_bytes_to_rpi(s_voice_buf, s_voice_len + 3);
                    s_fsm_state = FSM_IDLE;
                }
                break;

            case FSM_READ_TEXT:
                if (b == '\n' || b == '\r') {
                    s_txt_buf[s_txt_idx] = '\0';
                    if (strcmp(s_txt_buf, "$CALL_START") == 0) {
                        s_voice_call_mode = true;
                        if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                            s_rx_radar_data.emergency_code = 1;
                            xSemaphoreGive(s_state_mutex);
                        }
                    } else if (strcmp(s_txt_buf, "$CALL_END") == 0) {
                        s_voice_call_mode = false;
                        if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                            s_rx_radar_data.emergency_code = 0;
                            xSemaphoreGive(s_state_mutex);
                        }
                        send_bytes_to_rpi("$CALL_END\n", 10);
                    }
                    s_fsm_state = FSM_IDLE;
                    s_txt_idx = 0;
                } else {
                    if (s_txt_idx < (int)sizeof(s_txt_buf) - 1) s_txt_buf[s_txt_idx++] = (char)b;
                }
                break;
            }
        }
    }
}

static void handle_rpi_rx(void) {
    static uint8_t rpi_buf[256];
    static int rpi_len = 0;

    uint8_t temp[64];
    int len = uart_read_bytes(RPI_UART_NUM, temp, sizeof(temp), 0);

    if (len > 0) {
        if (rpi_len + len < (int)sizeof(rpi_buf)) {
            memcpy(&rpi_buf[rpi_len], temp, len);
            rpi_len += len;
        } else {
            rpi_len = 0;
        }
    }

    while (rpi_len > 0) {
        if (rpi_len >= 3 && rpi_buf[0] == 0x5A && rpi_buf[1] == 0xA5) {
            uint8_t c2_len = rpi_buf[2];
            if (rpi_len >= 3 + c2_len) {
                if (s_wroom_tx_mutex && xSemaphoreTake(s_wroom_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
                    uart_write_bytes(WROOM_CTRL_UART_NUM, (const char *)rpi_buf, 3 + c2_len);
                    xSemaphoreGive(s_wroom_tx_mutex);
                }
                rpi_len -= (3 + c2_len);
                if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[3 + c2_len], rpi_len);
                continue;
            } else {
                break;
            }
        }

        if (rpi_len >= 9 && memcmp(rpi_buf, "$CALL_END", 9) == 0) {
            send_to_wroom("$CALL_END\n");
            s_voice_call_mode = false;
            if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                s_rx_radar_data.emergency_code = 0;
                xSemaphoreGive(s_state_mutex);
            }
            rpi_len -= 9;
            if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[9], rpi_len);
            continue;
        }
        if (rpi_len >= 11 && memcmp(rpi_buf, "$CALL_START", 11) == 0) {
            send_to_wroom("$CALL_START\n");
            s_voice_call_mode = true;
            if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                s_rx_radar_data.emergency_code = 1;
                xSemaphoreGive(s_state_mutex);
            }
            rpi_len -= 11;
            if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[11], rpi_len);
            continue;
        }

        if (rpi_len >= 2) {
            uint8_t rx_msb = rpi_buf[0];
            uint8_t rx_lsb = rpi_buf[1];
            uint8_t target_rail = rx_msb & 0x0F;

            if (target_rail == 0 || target_rail == MY_RAIL_SEQ) {
                if (rx_lsb == 0xFF) {
                    radar_rx_frame_t snap;
                    if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                        snap = s_rx_radar_data;
                        xSemaphoreGive(s_state_mutex);
                    }

                    uint8_t curr_msb = ((s_power_supply_mode & 0x03) << 6) | (MY_RAIL_SEQ & 0x0F);
                    uint8_t rep_cat  = (s_current_category == 3) ? 2 : s_current_category;
                    uint8_t rep_sub  = (rep_cat == 2) ? s_music_led_pattern : s_current_sub_mode;
                    uint8_t curr_lsb = ((s_is_sleep_mode ? 1 : 0) << 7) |
                                       ((s_is_projector_on ? 1 : 0) << 6) |
                                       ((rep_cat & 0x03) << 4) | (rep_sub & 0x0F);

                    uint8_t raw[39] = {0};
                    raw[0] = (uint8_t)MY_RAIL_SEQ;
                    raw[1] = (uint8_t)((s_latest_l_mw >> 8) & 0xFF); raw[2] = (uint8_t)(s_latest_l_mw & 0xFF);
                    raw[3] = (uint8_t)((s_latest_r_mw >> 8) & 0xFF); raw[4] = (uint8_t)(s_latest_r_mw & 0xFF);
                    raw[5] = curr_msb; raw[6] = curr_lsb; raw[7] = s_latest_bat_pct;
                    raw[8] = (uint8_t)((snap.in_count >> 8) & 0xFF); raw[9] = (uint8_t)(snap.in_count & 0xFF);
                    raw[10] = (uint8_t)((snap.out_count >> 8) & 0xFF); raw[11] = (uint8_t)(snap.out_count & 0xFF);

                    for (int k = 0; k < 3; k++) {
                        raw[12 + (k*2)] = (uint8_t)((snap.r1_x[k] >> 8) & 0xFF); raw[13 + (k*2)] = (uint8_t)(snap.r1_x[k] & 0xFF);
                        raw[18 + (k*2)] = (uint8_t)((snap.r1_y[k] >> 8) & 0xFF); raw[19 + (k*2)] = (uint8_t)(snap.r1_y[k] & 0xFF);
                        raw[24 + (k*2)] = (uint8_t)((snap.r2_x[k] >> 8) & 0xFF); raw[25 + (k*2)] = (uint8_t)(snap.r2_x[k] & 0xFF);
                        raw[30 + (k*2)] = (uint8_t)((snap.r2_y[k] >> 8) & 0xFF); raw[31 + (k*2)] = (uint8_t)(snap.r2_y[k] & 0xFF);
                    }
                    raw[36] = snap.r1_detected; raw[37] = snap.r2_detected;
                    raw[38] = s_voice_call_mode ? 1 : snap.emergency_code;

                    uint8_t tf_encoded[39];
                    for (int j = 0; j < 39; j++) tf_encoded[j] = (uint8_t)((raw[j] + 0x20) & 0xFF);
                    send_bytes_to_rpi(tf_encoded, 39);

                    rpi_len -= 2;
                    if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[2], rpi_len);
                    continue;
                }

                s_power_supply_mode = (rx_msb >> 6) & 0x03;
                s_is_sleep_mode = (rx_lsb >> 7) & 0x01;
                s_is_projector_on = (rx_lsb >> 6) & 0x01;
                uint8_t new_cat = (rx_lsb >> 4) & 0x03;
                uint8_t new_sub = rx_lsb & 0x0F;

                if (new_cat == 2) {
                    s_current_category = 2;
                    if (new_sub <= 2) {
                        s_music_led_pattern = new_sub;
                    } else if (new_sub >= 3 && new_sub <= 12) {
                        s_current_volume = (new_sub - 2) * 10;
                        char cmd[32];
                        snprintf(cmd, sizeof(cmd), "$CTRL,%d,%d,%d\n", s_current_volume, s_play_mode, s_target_track);
                        send_to_wroom(cmd);
                    } else if (new_sub == 13) {
                        s_play_mode = 0;
                        char cmd[32];
                        snprintf(cmd, sizeof(cmd), "$CTRL,%d,0,%d\n", s_current_volume, s_target_track);
                        send_to_wroom(cmd);
                    } else if (new_sub == 14) {
                        s_play_mode = 1;
                        char cmd[32];
                        snprintf(cmd, sizeof(cmd), "$CTRL,%d,1,%d\n", s_current_volume, s_target_track);
                        send_to_wroom(cmd);
                    }
                } else if (new_cat == 3) {
                    s_current_category = 2;
                    if (new_sub >= 1 && new_sub <= 15) {
                        s_target_track = new_sub;
                        s_play_mode = 2;
                        char cmd[32];
                        snprintf(cmd, sizeof(cmd), "$CTRL,%d,2,%d\n", s_current_volume, s_target_track);
                        send_to_wroom(cmd);
                    }
                } else {
                    if (s_current_category == 2 || s_current_category == 3) {
                        send_to_wroom("$MUSIC,OFF\n");
                        s_is_music_on = false;
                    }
                    s_current_category = new_cat;
                    s_current_sub_mode = new_sub;
                }

                uint8_t ack[2] = {(uint8_t)MY_RAIL_SEQ, rx_lsb};
                send_bytes_to_rpi(ack, 2);

                rpi_len -= 2;
                if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[2], rpi_len);
                continue;
            }
        }

        rpi_len -= 1;
        memmove(rpi_buf, &rpi_buf[1], rpi_len);
    }
}

static void comm_task(void *pvParameters) {
    while (1) {
        handle_wroom_stream_rx();
        handle_rpi_rx();
        // [수정] 10ms (1틱) 명시적 딜레이를 주어 IDLE1 태스크의 WDT 갱신을 100% 보장
        vTaskDelay(pdMS_TO_TICKS(10));
    }
}

static void presentation_task(void *pvParameters) {
    int64_t last_bat_check = 0;
    while (1) {
        int64_t now = millis();
        if (now - last_bat_check >= 1000) {
            last_bat_check = now;
            read_battery_and_calculate_pct();
        }
        update_led_sequence();
        vTaskDelay(pdMS_TO_TICKS(10));
    }
}

static void init_uarts(void) {
    uart_config_t uart_cfg_115200 = {
        .baud_rate = 115200, .data_bits = UART_DATA_8_BITS, .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1, .flow_ctrl = UART_HW_FLOWCTRL_DISABLE, .source_clk = UART_SCLK_DEFAULT,
    };
    uart_config_t uart_cfg_9600 = {
        .baud_rate = 9600, .data_bits = UART_DATA_8_BITS, .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1, .flow_ctrl = UART_HW_FLOWCTRL_DISABLE, .source_clk = UART_SCLK_DEFAULT,
    };

    ESP_ERROR_CHECK(uart_driver_install(RPI_UART_NUM, UART_BUF_SIZE * 2, UART_BUF_SIZE * 2, 0, NULL, 0));
    ESP_ERROR_CHECK(uart_param_config(RPI_UART_NUM, &uart_cfg_9600));
    ESP_ERROR_CHECK(uart_set_pin(RPI_UART_NUM, RPI_TX_PIN, RPI_RX_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));

    ESP_ERROR_CHECK(uart_driver_install(WROOM_CTRL_UART_NUM, UART_BUF_SIZE * 2, UART_BUF_SIZE * 2, 0, NULL, 0));
    ESP_ERROR_CHECK(uart_param_config(WROOM_CTRL_UART_NUM, &uart_cfg_115200));
    ESP_ERROR_CHECK(uart_set_pin(WROOM_CTRL_UART_NUM, WROOM_CTRL_TX_PIN, WROOM_CTRL_RX_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));
}

static void init_i2c_bus(void) {
    i2c_master_bus_config_t bus_config = {
        .i2c_port = I2C_NUM_0, .sda_io_num = I2C_SDA_PIN, .scl_io_num = I2C_SCL_PIN,
        .clk_source = I2C_CLK_SRC_DEFAULT, .glitch_ignore_cnt = 7, .flags.enable_internal_pullup = true,
    };
    ESP_ERROR_CHECK(i2c_new_master_bus(&bus_config, &s_i2c_bus_handle));

    i2c_device_config_t dev_cfg_left = {
        .dev_addr_length = I2C_ADDR_BIT_LEN_7, .device_address = INA219_ADDR_LEFT, .scl_speed_hz = I2C_FREQ_HZ,
    };
    i2c_device_config_t dev_cfg_right = {
        .dev_addr_length = I2C_ADDR_BIT_LEN_7, .device_address = INA219_ADDR_RIGHT, .scl_speed_hz = I2C_FREQ_HZ,
    };

    if (i2c_master_bus_add_device(s_i2c_bus_handle, &dev_cfg_left, &s_ina_dev_left) == ESP_OK) {
        s_is_left_ina_ready = (init_ina219_dev(s_ina_dev_left) == ESP_OK);
    }
    if (i2c_master_bus_add_device(s_i2c_bus_handle, &dev_cfg_right, &s_ina_dev_right) == ESP_OK) {
        s_is_right_ina_ready = (init_ina219_dev(s_ina_dev_right) == ESP_OK);
    }
}

static void init_led_strips(void) {
    led_strip_config_t strip_config = { .strip_gpio_num = DATA_PIN_1, .max_leds = NUM_LEDS, .led_model = LED_MODEL_WS2812 };
    led_strip_rmt_config_t rmt_config = { .resolution_hz = 10 * 1000 * 1000 };
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &s_strip1));

    strip_config.strip_gpio_num = DATA_PIN_2;
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &s_strip2));

    clear_all_leds();
    flush_led_strips();
}

void app_main(void) {
    s_state_mutex = xSemaphoreCreateMutex();
    s_wroom_tx_mutex = xSemaphoreCreateMutex();
    s_rpi_tx_mutex = xSemaphoreCreateMutex();

    init_uarts();
    init_i2c_bus();
    init_led_strips();

    read_battery_and_calculate_pct();

    ESP_LOGI(TAG, "🚀 ESP32-P4 Codec2(2400bps) PLC 패스스루 가동 (Rail: %d)", MY_RAIL_SEQ);

    xTaskCreatePinnedToCore(comm_task, "comm_task", 4096, NULL, 5, NULL, 1);
    xTaskCreatePinnedToCore(presentation_task, "pres_task", 4096, NULL, 4, NULL, 0);
}