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

// UART_NUM_1 : 라즈베리파이 PLC 메인 통신 (@ 9600)
#define RPI_UART_NUM         UART_NUM_1
#define RPI_TX_PIN           48
#define RPI_RX_PIN           47

// UART_NUM_2 : WROOM 메인 통합 통신 (오디오 + 레이더 바이너리 @ 115200)
#define WROOM_CTRL_UART_NUM  UART_NUM_2
#define WROOM_CTRL_TX_PIN    53
#define WROOM_CTRL_RX_PIN    54

#define UART_BUF_SIZE        1024

// 릴레이 핀
#define RELAY_PIN            GPIO_NUM_2
#define PROJECTOR_PIN        GPIO_NUM_11

// 네오픽셀 RMT 핀 설정
#define DATA_PIN_1           GPIO_NUM_4
#define DATA_PIN_2           GPIO_NUM_5
#define NUM_ROWS             4
#define LEDS_PER_ROW         31
#define NUM_LEDS             (LEDS_PER_ROW * NUM_ROWS)

// I2C INA219 설정
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
static volatile int      s_target_track      = 1;

static volatile uint8_t  s_latest_bat_pct    = 0;
static volatile uint16_t s_latest_l_mw       = 0;
static volatile uint16_t s_latest_r_mw       = 0;
static uint32_t          s_anim_frame        = 0;

static volatile int64_t  s_sleep_wake_timer  = 0;
#define HOLD_TIME_MS     10000

static volatile bool     s_system_power_state = true;
static bool              s_last_power_state   = true;

#define NUM_COLUMNS 8
static const uint8_t RAIN_COLUMNS[NUM_COLUMNS] = {2, 6, 10, 14, 18, 22, 26, 29};
typedef enum { STATE_WAITING, STATE_FALLING } drop_state_t;
static drop_state_t s_column_state[NUM_COLUMNS];
static int64_t s_column_next_drop[NUM_COLUMNS] = {0};

static uint8_t s_audio_bands[8] = {0};
static float s_smooth_bass = 0.0f;
static float s_smooth_acoustic = 0.0f;
static float s_peak_bass_max = 2.0f;
static float s_peak_acoustic_max = 2.0f;

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

static void hsv2rgb(uint16_t hue, uint8_t sat, uint8_t val, uint8_t *r, uint8_t *g, uint8_t *b) {
    uint8_t region = hue / 43;
    uint8_t remainder = (hue - (region * 43)) * 6;

    uint8_t p = (val * (255 - sat)) >> 8;
    uint8_t q = (val * (255 - ((sat * remainder) >> 8))) >> 8;
    uint8_t t = (val * (255 - ((sat * (255 - remainder)) >> 8))) >> 8;

    switch (region) {
        case 0:  *r = val; *g = t;   *b = p;   break;
        case 1:  *r = q;   *g = val; *b = p;   break;
        case 2:  *r = p;   *g = val; *b = t;   break;
        case 3:  *r = p;   *g = q;   *b = val; break;
        case 4:  *r = t;   *g = p;   *b = val; break;
        default: *r = val; *g = p;   *b = q;   break;
    }
}

static uint16_t get_pixel_index(uint8_t row, uint8_t col) {
    if (row >= NUM_ROWS || col >= LEDS_PER_ROW) return 0;
    if (row % 2 == 1) col = (LEDS_PER_ROW - 1) - col;
    return (row * LEDS_PER_ROW) + col;
}

static void set_pixel1(uint8_t row, uint8_t col, uint8_t r, uint8_t g, uint8_t b) {
    uint16_t idx = get_pixel_index(row, col);
    if (idx < NUM_LEDS) {
        s_fb1[idx][0] = r; s_fb1[idx][1] = g; s_fb1[idx][2] = b;
    }
}

static void set_pixel2(uint8_t row, uint8_t col, uint8_t r, uint8_t g, uint8_t b) {
    uint16_t idx = get_pixel_index(row, col);
    if (idx < NUM_LEDS) {
        s_fb2[idx][0] = r; s_fb2[idx][1] = g; s_fb2[idx][2] = b;
    }
}

static void set_pixel_2d_cyan(uint8_t row, uint8_t col) {
    set_pixel1(row, col, 255, 0, 255);
    set_pixel2(row, col, 0, 255, 255);
}

static void clear_all_leds(void) {
    memset(s_fb1, 0, sizeof(s_fb1));
    memset(s_fb2, 0, sizeof(s_fb2));
}

static bool is_column_active(uint8_t col) {
    for (uint8_t r = 0; r < NUM_ROWS; r++) {
        uint16_t idx = get_pixel_index(r, col);
        if ((s_fb1[idx][0] | s_fb1[idx][1] | s_fb1[idx][2]) > 0 ||
            (s_fb2[idx][0] | s_fb2[idx][1] | s_fb2[idx][2]) > 0) return true;
    }
    return false;
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
    bool need_show = false;

    if (s_current_category == 0) {
        switch (s_current_sub_mode) {
            case 1:
                if (current_millis - last_led_update > 10) {
                    last_led_update = current_millis;
                    uint8_t base_hue = (uint8_t)(s_anim_frame * 2);
                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                            uint8_t h = base_hue + (c * 8) + (r * 32);
                            uint8_t cr, cg, cb;
                            hsv2rgb(h, 240, 200, &cr, &cg, &cb);
                            set_pixel1(r, c, cr, cg, cb);
                            set_pixel2(r, c, cr, cg, cb);
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 2:
                if (current_millis - last_led_update > 80) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    uint8_t active_row = (s_anim_frame / 2) % (NUM_ROWS * 2 - 2);
                    if (active_row >= NUM_ROWS) active_row = (NUM_ROWS * 2 - 2) - active_row;
                    for (uint8_t c = 0; c < LEDS_PER_ROW; c++) set_pixel_2d_cyan(active_row, c);
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 3:
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
                    need_show = true;
                }
                break;
            case 4:
                if (current_millis - last_led_update > 10) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    uint16_t head = s_anim_frame % NUM_LEDS;
                    for (uint8_t i = 0; i < 20; i++) {
                        int pixel_idx = (head - i + NUM_LEDS) % NUM_LEDS;
                        uint8_t bright = (20 - i) * 255 / 20;
                        s_fb1[pixel_idx][0] = bright / 2; s_fb1[pixel_idx][1] = bright; s_fb1[pixel_idx][2] = 0;
                        s_fb2[pixel_idx][0] = bright;     s_fb2[pixel_idx][1] = bright / 2; s_fb2[pixel_idx][2] = 0;
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 5:
                if (current_millis - last_led_update > 30) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    uint8_t step = s_anim_frame % 16;
                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        uint8_t g_val = (step * 10 < 150) ? (150 - step * 10) : 0;
                        if (15 - step >= 0) {
                            set_pixel1(r, 15 - step, g_val, 255, 0);
                            set_pixel2(r, 15 - step, 255, g_val, 0);
                        }
                        if (15 + step < LEDS_PER_ROW) {
                            set_pixel1(r, 15 + step, g_val, 255, 0);
                            set_pixel2(r, 15 + step, 255, g_val, 0);
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 6:
                if (current_millis - last_led_update > 60) {
                    last_led_update = current_millis;
                    for (int i = 0; i < NUM_LEDS; i++) {
                        s_fb1[i][0] = s_fb1[i][0] * 70 / 100;
                        s_fb1[i][1] = s_fb1[i][1] * 70 / 100;
                        s_fb1[i][2] = s_fb1[i][2] * 70 / 100;
                        s_fb2[i][0] = s_fb2[i][0] * 70 / 100;
                        s_fb2[i][1] = s_fb2[i][1] * 70 / 100;
                        s_fb2[i][2] = s_fb2[i][2] * 70 / 100;
                    }
                    for (int r = 0; r < NUM_ROWS - 1; r++) {
                        for (int c = 0; c < LEDS_PER_ROW; c++) {
                            uint16_t up = get_pixel_index(r + 1, c);
                            if ((s_fb1[up][0] | s_fb1[up][1] | s_fb1[up][2]) > 0) {
                                set_pixel1(r, c, s_fb1[up][0], s_fb1[up][1], s_fb1[up][2]);
                            }
                            if ((s_fb2[up][0] | s_fb2[up][1] | s_fb2[up][2]) > 0) {
                                set_pixel2(r, c, s_fb2[up][0], s_fb2[up][1], s_fb2[up][2]);
                            }
                        }
                    }
                    for (uint8_t i = 0; i < NUM_COLUMNS; i++) {
                        uint8_t col = RAIN_COLUMNS[i];
                        if (s_column_state[i] == STATE_FALLING && !is_column_active(col)) {
                            s_column_state[i] = STATE_WAITING;
                            s_column_next_drop[i] = current_millis + (rand() % 2500 + 1000);
                        }
                        if (s_column_state[i] == STATE_WAITING && current_millis >= s_column_next_drop[i]) {
                            set_pixel_2d_cyan(NUM_ROWS - 1, col);
                            s_column_state[i] = STATE_FALLING;
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 7:
                if (current_millis - last_led_update > 250) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    bool phase = (s_anim_frame % 2 == 0);
                    for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                        set_pixel1(0, c, phase ? 0 : 200, phase ? 180 : 0, phase ? 255 : 0);
                        set_pixel2(0, c, phase ? 180 : 255, phase ? 0 : 200, phase ? 255 : 0);
                        set_pixel1(1, c, phase ? 200 : 0, phase ? 255 : 180, phase ? 0 : 255);
                        set_pixel2(1, c, phase ? 255 : 180, phase ? 200 : 0, phase ? 0 : 255);
                        set_pixel1(2, c, phase ? 0 : 200, phase ? 180 : 0, phase ? 255 : 0);
                        set_pixel2(2, c, phase ? 180 : 255, phase ? 0 : 200, phase ? 255 : 0);
                        set_pixel1(3, c, phase ? 200 : 0, phase ? 255 : 180, phase ? 0 : 255);
                        set_pixel2(3, c, phase ? 255 : 180, phase ? 200 : 0, phase ? 0 : 255);
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            default:
                clear_all_leds();
                need_show = true;
                break;
        }
    } else if (s_current_category == 1) {
        switch (s_current_sub_mode) {
            case 1:
                if (current_millis - last_led_update > 30) {
                    last_led_update = current_millis;
                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                            uint8_t bright = sine8((c * 10) + (s_anim_frame * 2));
                            set_pixel1(r, c, bright, (uint8_t)(bright * 7 / 10), 0);
                            set_pixel2(r, c, bright, (uint8_t)(bright * 7 / 10), 0);
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 2:
                if (current_millis - last_led_update > 40) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                            if ((c + r) % 5 == (s_anim_frame % 5)) {
                                set_pixel1(r, c, 0, 180, 255);
                                set_pixel2(r, c, 0, 255, 200);
                            }
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            default:
                if (current_millis - last_led_update > 50) {
                    last_led_update = current_millis;
                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                            uint8_t bright = sine8((c * 8) + (r * 20) + s_anim_frame);
                            set_pixel1(r, c, bright / 2, bright / 2, bright / 2);
                            set_pixel2(r, c, bright / 2, bright / 2, bright / 2);
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
        }
    } else if (s_current_category == 2 || s_current_category == 3) {
        switch (s_music_led_pattern) {
            case 0:
                if (current_millis - last_led_update > 15) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    float overall_audio = (s_audio_bands[0] * 0.45f) + (s_audio_bands[1] * 0.25f) +
                                          (s_audio_bands[2] * 0.18f) + (s_audio_bands[3] * 0.12f);
                    if (overall_audio == 0.0f) {
                        uint8_t d_sin = sine8(s_anim_frame * 3);
                        overall_audio = (d_sin > 110) ? ((float)(d_sin - 110) * 3.0f / 145.0f + 1.0f) : 0.0f;
                    }
                    if (overall_audio > s_peak_acoustic_max) s_peak_acoustic_max = overall_audio;
                    else {
                        s_peak_acoustic_max = (s_peak_acoustic_max * 0.995f) + (overall_audio * 0.005f);
                        if (s_peak_acoustic_max < 2.0f) s_peak_acoustic_max = 2.0f;
                    }

                    float norm_audio = overall_audio / s_peak_acoustic_max;
                    if (norm_audio > 1.0f) norm_audio = 1.0f;
                    if (norm_audio > s_smooth_acoustic) s_smooth_acoustic = norm_audio;
                    else s_smooth_acoustic *= 0.94f;

                    float active_radius = 12.0f + (s_smooth_acoustic * 3.0f);
                    float max_h = s_smooth_acoustic * (NUM_ROWS - 0.01f);

                    for (uint8_t c = 0; c < LEDS_PER_ROW; c++) {
                        float dist = fabsf((float)c - 15.0f);
                        if (dist <= active_radius) {
                            float norm_dist = dist / active_radius;
                            float profile = 1.0f - (0.85f * norm_dist * norm_dist);
                            float ripple = ((float)sine8(c * 15 + s_anim_frame * 4) - 128.0f) / 255.0f * 0.45f * (s_smooth_acoustic + 0.3f);
                            float raw_h = (max_h * profile) + ripple;
                            if (raw_h < 0.2f) raw_h = 0.2f;
                            uint8_t full_rows = (uint8_t)raw_h;
                            float row_frac = raw_h - full_rows;

                            for (uint8_t r = 0; r <= full_rows && r < NUM_ROWS; r++) {
                                float alpha = (r == full_rows) ? row_frac : 1.0f;
                                if (alpha <= 0.05f && r == full_rows) continue;
                                float base_a = (r == 0) ? (0.75f + 0.25f * (sine8(c * 12 + s_anim_frame * 3) / 255.0f)) * alpha : alpha;
                                uint8_t hue = (c * 5 + r * 15 + s_anim_frame * 2) % 256;
                                uint8_t cr, cg, cb;
                                hsv2rgb(hue, 230, (uint8_t)(255 * base_a), &cr, &cg, &cb);
                                set_pixel1(r, c, cr, cg, cb);
                                set_pixel2(r, c, cr, cg, cb);
                            }
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            case 1:
                if (current_millis - last_led_update > 12) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    float bass_val = (float)s_audio_bands[0];
                    float mid_val  = (float)s_audio_bands[1];
                    float raw_bass = (bass_val * 0.85f) + (mid_val * 0.15f);

                    if (raw_bass == 0.0f) {
                        uint8_t d_sin = sine8(s_anim_frame * 2);
                        raw_bass = (d_sin > 130) ? ((float)(d_sin - 130) * 4.0f / 125.0f) : 0.0f;
                    }
                    if (raw_bass > s_peak_bass_max) s_peak_bass_max = raw_bass;
                    else {
                        s_peak_bass_max = (s_peak_bass_max * 0.995f) + (raw_bass * 0.005f);
                        if (s_peak_bass_max < 2.0f) s_peak_bass_max = 2.0f;
                    }

                    float norm_bass = raw_bass / s_peak_bass_max;
                    if (norm_bass > 1.0f) norm_bass = 1.0f;
                    if (norm_bass > s_smooth_bass) s_smooth_bass = norm_bass;
                    else s_smooth_bass *= 0.955f;

                    float impact = s_smooth_bass * s_smooth_bass;
                    bool is_kick = (bass_val >= 3.0f);

                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        float min_len = (r == 1 || r == 2) ? 4.0f : 0.8f;
                        float max_len = (r == 1 || r == 2) ? 31.0f : 18.0f;
                        float cur_len = min_len + impact * (max_len - min_len);
                        uint8_t full_pix = (uint8_t)cur_len;
                        float frac = cur_len - full_pix;

                        for (uint8_t c = 0; c <= full_pix && c < LEDS_PER_ROW; c++) {
                            float alpha = (c == full_pix) ? frac : 1.0f;
                            uint8_t stream_wave = sine8((c * 18) - (s_anim_frame * 2));
                            uint8_t bright = (uint8_t)(((stream_wave * 115 / 255) + 140) * alpha);
                            uint8_t hue = (130 + (c * 2) + s_anim_frame) % 256;
                            uint8_t cr, cg, cb;
                            if (is_kick && c <= 2) { cr = 230; cg = 255; cb = 255; }
                            else { hsv2rgb(hue, 220, bright, &cr, &cg, &cb); }
                            set_pixel1(r, c, cr, cg, cb);
                            set_pixel2(r, c, cr, cg, cb);
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
            default:
                if (current_millis - last_led_update > 12) {
                    last_led_update = current_millis;
                    clear_all_leds();
                    float bass_val = (float)s_audio_bands[0];
                    float mid_val  = (float)s_audio_bands[1];
                    float raw_lvl  = (bass_val * 0.85f) + (mid_val * 0.15f);

                    if (raw_lvl == 0.0f) {
                        uint8_t d_sin = sine8(s_anim_frame * 2);
                        raw_lvl = (d_sin > 140) ? ((float)(d_sin - 140) * 3.5f / 115.0f) : 0.0f;
                    }
                    if (raw_lvl > s_peak_acoustic_max) s_peak_acoustic_max = raw_lvl;
                    else {
                        s_peak_acoustic_max = (s_peak_acoustic_max * 0.995f) + (raw_lvl * 0.005f);
                        if (s_peak_acoustic_max < 2.0f) s_peak_acoustic_max = 2.0f;
                    }

                    float norm_lvl = raw_lvl / s_peak_acoustic_max;
                    if (norm_lvl > 1.0f) norm_lvl = 1.0f;
                    if (norm_lvl > s_smooth_acoustic) s_smooth_acoustic = norm_lvl;
                    else s_smooth_acoustic *= 0.955f;

                    float impact = s_smooth_acoustic * s_smooth_acoustic;
                    bool is_kick = (bass_val >= 3.0f);
                    float center_col = 15.0f;

                    for (uint8_t r = 0; r < NUM_ROWS; r++) {
                        float min_rad = (r == 1 || r == 2) ? 4.5f : 0.8f;
                        float max_rad = (r == 1 || r == 2) ? 15.0f : 8.5f;
                        float cur_rad = min_rad + impact * (max_rad - min_rad);
                        uint8_t full_rad = (uint8_t)cur_rad;
                        float frac = cur_rad - full_rad;

                        for (uint8_t dist = 0; dist <= full_rad && dist <= 15; dist++) {
                            int left_c = (int)(center_col - dist);
                            int right_c = (int)(center_col + dist);
                            float alpha = (dist == full_rad) ? frac : 1.0f;
                            uint8_t wave_dim = sine8((dist * 22) - (s_anim_frame * 2));
                            uint8_t bright = (uint8_t)(((wave_dim * 125 / 255) + 130) * alpha);
                            uint8_t hue = (s_anim_frame + dist * 6) % 256;
                            uint8_t cr, cg, cb;
                            if (is_kick && dist <= 3) { cr = 255; cg = 255; cb = 230; }
                            else { hsv2rgb(hue, is_kick ? 180 : 230, bright, &cr, &cg, &cb); }

                            if (left_c >= 0 && left_c < LEDS_PER_ROW) {
                                set_pixel1(r, left_c, cr, cg, cb); set_pixel2(r, left_c, cr, cg, cb);
                            }
                            if (right_c >= 0 && right_c < LEDS_PER_ROW) {
                                set_pixel1(r, right_c, cr, cg, cb); set_pixel2(r, right_c, cr, cg, cb);
                            }
                        }
                    }
                    s_anim_frame++;
                    need_show = true;
                }
                break;
        }
    }

    if (need_show) {
        flush_led_strips();
    }
}

static esp_err_t ina219_read_reg(i2c_master_dev_handle_t dev_handle, uint8_t reg, uint16_t *val) {
    if (!dev_handle) return ESP_FAIL;
    uint8_t buf[2];
    esp_err_t ret = i2c_master_transmit_receive(dev_handle, &reg, 1, buf, 2, pdMS_TO_TICKS(50));
    if (ret == ESP_OK) {
        *val = (buf[0] << 8) | buf[1];
    }
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

static void update_power_relay_only(void) {
    if (s_power_supply_mode == 2) gpio_set_level(RELAY_PIN, 1);
    else if (s_power_supply_mode == 1) gpio_set_level(RELAY_PIN, 0);
    else {
        if (s_latest_bat_pct <= 20) gpio_set_level(RELAY_PIN, 1);
        else if (s_latest_bat_pct >= 90) gpio_set_level(RELAY_PIN, 0);
    }
}

static void send_to_wroom(const char *cmd) {
    if (s_wroom_tx_mutex && xSemaphoreTake(s_wroom_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        uart_write_bytes(WROOM_CTRL_UART_NUM, cmd, strlen(cmd));
        xSemaphoreGive(s_wroom_tx_mutex);
    }
}

typedef enum {
    FSM_IDLE,
    FSM_FIND_55,
    FSM_READ_BODY,
    FSM_READ_TEXT
} unified_fsm_t;

static void handle_wroom_stream_rx(void) {
    static unified_fsm_t s_fsm_state = FSM_IDLE;
    static uint8_t s_rx_buf[34];
    static int s_body_idx = 0;
    static char s_txt_buf[128];
    static int s_txt_idx = 0;

    uint8_t temp[128];
    int len = uart_read_bytes(WROOM_CTRL_UART_NUM, temp, sizeof(temp), 0);

    if (len > 0) {
        for (int i = 0; i < len; i++) {
            uint8_t b = temp[i];

            switch (s_fsm_state) {
            case FSM_IDLE:
                if (b == 0xAA) {
                    s_rx_buf[0] = 0xAA;
                    s_fsm_state = FSM_FIND_55;
                } else if (b == '$') {
                    s_txt_idx = 0;
                    s_txt_buf[s_txt_idx++] = (char)b;
                    s_fsm_state = FSM_READ_TEXT;
                }
                break;

            case FSM_FIND_55:
                if (b == 0x55) {
                    s_rx_buf[1] = 0x55;
                    s_body_idx = 2;
                    s_fsm_state = FSM_READ_BODY;
                } else if (b == 0xAA) {
                    s_fsm_state = FSM_FIND_55;
                } else if (b == '$') {
                    s_txt_idx = 0;
                    s_txt_buf[s_txt_idx++] = (char)b;
                    s_fsm_state = FSM_READ_TEXT;
                } else {
                    s_fsm_state = FSM_IDLE;
                }
                break;

            case FSM_READ_BODY:
                s_rx_buf[s_body_idx++] = b;

                if (s_body_idx >= 34) {
                    uint8_t chk = 0;
                    for (int j = 2; j < 33; j++) {
                        chk ^= s_rx_buf[j];
                    }

                    if (chk == s_rx_buf[33]) {
                        radar_rx_frame_t temp_pkt;
                        temp_pkt.header1 = 0xAA;
                        temp_pkt.header2 = 0x55;
                        temp_pkt.in_count  = (s_rx_buf[2] << 8) | s_rx_buf[3];
                        temp_pkt.out_count = (s_rx_buf[4] << 8) | s_rx_buf[5];

                        for (int k = 0; k < 3; k++) {
                            temp_pkt.r1_x[k] = (int16_t)((s_rx_buf[6 + (k * 2)] << 8) | s_rx_buf[7 + (k * 2)]);
                            temp_pkt.r1_y[k] = (int16_t)((s_rx_buf[12 + (k * 2)] << 8) | s_rx_buf[13 + (k * 2)]);
                            temp_pkt.r2_x[k] = (int16_t)((s_rx_buf[18 + (k * 2)] << 8) | s_rx_buf[19 + (k * 2)]);
                            temp_pkt.r2_y[k] = (int16_t)((s_rx_buf[24 + (k * 2)] << 8) | s_rx_buf[25 + (k * 2)]);
                        }
                        temp_pkt.r1_detected    = s_rx_buf[30];
                        temp_pkt.r2_detected    = s_rx_buf[31];
                        temp_pkt.emergency_code = s_rx_buf[32];
                        temp_pkt.checksum       = s_rx_buf[33];

                        bool wake = (temp_pkt.emergency_code != 0) ||
                                    (temp_pkt.r1_detected == 1) ||
                                    (temp_pkt.r2_detected == 1);
                        for (int k = 0; k < 3; k++) {
                            if (abs(temp_pkt.r1_y[k]) > 100 || abs(temp_pkt.r2_y[k]) > 100) {
                                wake = true;
                                break;
                            }
                        }

                        if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                            s_rx_radar_data = temp_pkt;
                            if (wake) s_sleep_wake_timer = millis();
                            xSemaphoreGive(s_state_mutex);
                        }
                    }

                    s_fsm_state = FSM_IDLE;
                    s_body_idx = 0;
                }
                break;

            case FSM_READ_TEXT:
                if (b == '\n' || b == '\r') {
                    s_txt_buf[s_txt_idx] = '\0';
                    if (strncmp(s_txt_buf, "$AUDIO,", 7) == 0) {
                        int bands[8] = {0};
                        if (sscanf(s_txt_buf, "$AUDIO,%d,%d,%d,%d,%d,%d,%d,%d",
                                   &bands[0], &bands[1], &bands[2], &bands[3],
                                   &bands[4], &bands[5], &bands[6], &bands[7]) == 8) {
                            for (int j = 0; j < 8; j++) s_audio_bands[j] = (uint8_t)bands[j];
                        }
                    }
                    s_fsm_state = FSM_IDLE;
                    s_txt_idx = 0;
                } else {
                    if (s_txt_idx < (int)sizeof(s_txt_buf) - 1) {
                        s_txt_buf[s_txt_idx++] = (char)b;
                    } else {
                        s_fsm_state = FSM_IDLE;
                        s_txt_idx = 0;
                    }
                }
                break;
            }
        }
    }
}

// =============================================================
// 9. [0xFF 표준 폴링] 39바이트 +0x20 오프셋 완전체 원샷 송출
// =============================================================
static void handle_rpi_rx(void) {
    static uint8_t rpi_buf[32];
    static int rpi_len = 0;

    uint8_t temp[32];
    int len = uart_read_bytes(RPI_UART_NUM, temp, sizeof(temp), 0);

    if (len > 0) {
        for (int i = 0; i < len; i++) {
            if (rpi_len < (int)sizeof(rpi_buf)) {
                rpi_buf[rpi_len++] = temp[i];
            }
        }
    }

    while (rpi_len >= 2) {
        uint8_t rx_msb = rpi_buf[0];
        uint8_t rx_lsb = rpi_buf[1];
        uint8_t target_rail = rx_msb & 0x0F;

        if (target_rail == 0 || target_rail == MY_RAIL_SEQ) {
            
            // ---------------------------------------------------------
            // [A] 관제 데이터 요청 (0xFF) -> 39바이트 +0x20 인코딩 송출
            // ---------------------------------------------------------
            if (rx_lsb == 0xFF) {
                radar_rx_frame_t snap;
                if (xSemaphoreTake(s_state_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                    snap = s_rx_radar_data;
                    xSemaphoreGive(s_state_mutex);
                }

                uint16_t l_mw = s_latest_l_mw;
                uint16_t r_mw = s_latest_r_mw;

                uint8_t curr_msb = ((s_power_supply_mode & 0x03) << 6) | (MY_RAIL_SEQ & 0x0F);
                uint8_t rep_cat  = (s_current_category == 3) ? 2 : s_current_category;
                uint8_t rep_sub  = (rep_cat == 2) ? s_music_led_pattern : s_current_sub_mode;
                uint8_t curr_lsb = ((s_is_sleep_mode ? 1 : 0) << 7) |
                                   ((s_is_projector_on ? 1 : 0) << 6) |
                                   ((rep_cat & 0x03) << 4) |
                                   (rep_sub & 0x0F);

                uint8_t raw[39] = {0};
                raw[0]  = (uint8_t)MY_RAIL_SEQ;
                raw[1]  = (uint8_t)((l_mw >> 8) & 0xFF);
                raw[2]  = (uint8_t)(l_mw & 0xFF);
                raw[3]  = (uint8_t)((r_mw >> 8) & 0xFF);
                raw[4]  = (uint8_t)(r_mw & 0xFF);
                raw[5]  = curr_msb;
                raw[6]  = curr_lsb;
                raw[7]  = s_latest_bat_pct;
                raw[8]  = (uint8_t)((snap.in_count >> 8) & 0xFF);
                raw[9]  = (uint8_t)(snap.in_count & 0xFF);
                raw[10] = (uint8_t)((snap.out_count >> 8) & 0xFF);
                raw[11] = (uint8_t)(snap.out_count & 0xFF);

                // R1 X
                raw[12] = (uint8_t)((snap.r1_x[0] >> 8) & 0xFF);
                raw[13] = (uint8_t)(snap.r1_x[0] & 0xFF);
                raw[14] = (uint8_t)((snap.r1_x[1] >> 8) & 0xFF);
                raw[15] = (uint8_t)(snap.r1_x[1] & 0xFF);
                raw[16] = (uint8_t)((snap.r1_x[2] >> 8) & 0xFF);
                raw[17] = (uint8_t)(snap.r1_x[2] & 0xFF);

                // R1 Y
                raw[18] = (uint8_t)((snap.r1_y[0] >> 8) & 0xFF);
                raw[19] = (uint8_t)(snap.r1_y[0] & 0xFF);
                raw[20] = (uint8_t)((snap.r1_y[1] >> 8) & 0xFF);
                raw[21] = (uint8_t)(snap.r1_y[1] & 0xFF);
                raw[22] = (uint8_t)((snap.r1_y[2] >> 8) & 0xFF);
                raw[23] = (uint8_t)(snap.r1_y[2] & 0xFF);

                // R2 X
                raw[24] = (uint8_t)((snap.r2_x[0] >> 8) & 0xFF);
                raw[25] = (uint8_t)(snap.r2_x[0] & 0xFF);
                raw[26] = (uint8_t)((snap.r2_x[1] >> 8) & 0xFF);
                raw[27] = (uint8_t)(snap.r2_x[1] & 0xFF);
                raw[28] = (uint8_t)((snap.r2_x[2] >> 8) & 0xFF);
                raw[29] = (uint8_t)(snap.r2_x[2] & 0xFF);

                // R2 Y
                raw[30] = (uint8_t)((snap.r2_y[0] >> 8) & 0xFF);
                raw[31] = (uint8_t)(snap.r2_y[0] & 0xFF);
                raw[32] = (uint8_t)((snap.r2_y[1] >> 8) & 0xFF);
                raw[33] = (uint8_t)(snap.r2_y[1] & 0xFF);
                raw[34] = (uint8_t)((snap.r2_y[2] >> 8) & 0xFF);
                raw[35] = (uint8_t)(snap.r2_y[2] & 0xFF);

                raw[36] = snap.r1_detected;
                raw[37] = snap.r2_detected;
                raw[38] = snap.emergency_code;

                // 0x00 널 바이트를 원천 제거하기 위한 +0x20 오프셋 변환
                uint8_t tf_encoded[39];
                for (int i = 0; i < 39; i++) {
                    tf_encoded[i] = (uint8_t)((raw[i] + 0x20) & 0xFF);
                }

                uart_write_bytes(RPI_UART_NUM, (const char *)tf_encoded, 39);
                uart_wait_tx_done(RPI_UART_NUM, pdMS_TO_TICKS(50));

                rpi_len -= 2;
                if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[2], rpi_len);
                continue;
            }

            // ---------------------------------------------------------
            // [B] 16비트 웹 제어 명령 처리
            // ---------------------------------------------------------
            s_power_supply_mode = (rx_msb >> 6) & 0x03;
            bool new_sleep = (rx_lsb >> 7) & 0x01;
            if (new_sleep != s_is_sleep_mode) {
                s_is_sleep_mode = new_sleep;
                if (s_is_sleep_mode) {
                    s_sleep_wake_timer = millis() - HOLD_TIME_MS - 1000;
                    if (s_current_category == 2 || s_current_category == 3) {
                        send_to_wroom("$MUSIC,OFF\n");
                        s_is_music_on = false;
                    }
                } else {
                    s_sleep_wake_timer = millis();
                }
            }

            s_is_projector_on = (rx_lsb >> 6) & 0x01;
            uint8_t new_cat = (rx_lsb >> 4) & 0x03;
            uint8_t new_sub = rx_lsb & 0x0F;

            if (new_cat == 2) {
                bool was_not = (s_current_category != 2 && s_current_category != 3);
                s_current_category = 2;
                if (was_not) { s_anim_frame = 0; clear_all_leds(); }

                if (new_sub <= 2) {
                    if (s_music_led_pattern != new_sub || s_current_sub_mode != new_sub) {
                        s_music_led_pattern = new_sub;
                        s_current_sub_mode  = new_sub;
                        s_anim_frame = 0;
                        clear_all_leds();
                    }
                } else if (new_sub >= 3 && new_sub <= 12) {
                    s_current_volume = (new_sub - 2) * 10;
                    char cmd[32];
                    snprintf(cmd, sizeof(cmd), "$CTRL,%d,0,%d\n", s_current_volume, s_target_track);
                    send_to_wroom(cmd);
                } else if (new_sub == 13) {
                    char cmd[32];
                    snprintf(cmd, sizeof(cmd), "$CTRL,%d,0,%d\n", s_current_volume, s_target_track);
                    send_to_wroom(cmd);
                } else if (new_sub == 14) {
                    char cmd[32];
                    snprintf(cmd, sizeof(cmd), "$CTRL,%d,1,%d\n", s_current_volume, s_target_track);
                    send_to_wroom(cmd);
                }
            } else if (new_cat == 3) {
                bool was_not = (s_current_category != 2 && s_current_category != 3);
                s_current_category = 2;
                if (was_not) { s_anim_frame = 0; clear_all_leds(); }

                if (new_sub >= 1 && new_sub <= 15) {
                    s_target_track = new_sub;
                    char cmd[32];
                    snprintf(cmd, sizeof(cmd), "$CTRL,%d,2,%d\n", s_current_volume, s_target_track);
                    send_to_wroom(cmd);
                }
            } else {
                bool was_music = (s_current_category == 2 || s_current_category == 3);
                if (was_music) {
                    send_to_wroom("$MUSIC,OFF\n");
                    s_is_music_on = false;
                }
                if (new_cat != s_current_category || new_sub != s_current_sub_mode) {
                    s_current_category = new_cat;
                    s_current_sub_mode  = new_sub;
                    s_anim_frame = 0;
                    clear_all_leds();
                }
            }

            uint8_t ack[2] = {(uint8_t)MY_RAIL_SEQ, rx_lsb};
            uart_write_bytes(RPI_UART_NUM, (const char *)ack, 2);
            update_power_relay_only();

            rpi_len -= 2;
            if (rpi_len > 0) memmove(rpi_buf, &rpi_buf[2], rpi_len);
            continue;
        }

        rpi_len -= 1;
        memmove(rpi_buf, &rpi_buf[1], rpi_len);
    }
}

static void comm_task(void *pvParameters) {
    while (1) {
        handle_wroom_stream_rx();
        handle_rpi_rx();
        vTaskDelay(pdMS_TO_TICKS(10) > 0 ? pdMS_TO_TICKS(10) : 1);
    }
}

static void presentation_task(void *pvParameters) {
    int64_t last_bat_check = 0;

    while (1) {
        int64_t now = millis();

        if (now - last_bat_check >= 1000) {
            last_bat_check = now;
            read_battery_and_calculate_pct();
            update_power_relay_only();
        }

        if (s_is_sleep_mode) {
            s_system_power_state = (now - s_sleep_wake_timer < HOLD_TIME_MS);
        } else {
            s_system_power_state = true;
        }

        if (s_system_power_state != s_last_power_state) {
            s_last_power_state = s_system_power_state;
            if (s_system_power_state) {
                ESP_LOGI(TAG, "☀️ [SYSTEM WAKE] 시스템 가동");
                s_is_music_on = false;
            } else {
                ESP_LOGI(TAG, "🌙 [SYSTEM SLEEP] 시스템 소등");
                if (s_current_category == 2 || s_current_category == 3) {
                    send_to_wroom("$MUSIC,OFF\n");
                    s_is_music_on = false;
                }
                memset(s_audio_bands, 0, sizeof(s_audio_bands));
                clear_all_leds();
                flush_led_strips();
                gpio_set_level(PROJECTOR_PIN, 0);
            }
        }

        if (s_system_power_state) {
            update_led_sequence();
            gpio_set_level(PROJECTOR_PIN, s_is_projector_on ? 1 : 0);

            if ((s_current_category == 2 || s_current_category == 3) && !s_is_music_on) {
                send_to_wroom("$MUSIC,ON\n");
                s_is_music_on = true;
            }
        }

        vTaskDelay(pdMS_TO_TICKS(10) > 0 ? pdMS_TO_TICKS(10) : 1);
    }
}

static void init_uarts(void) {
    uart_config_t uart_cfg_115200 = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_8_BITS,
        .parity    = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_DEFAULT,
    };

    uart_config_t uart_cfg_9600 = {
        .baud_rate = 9600,
        .data_bits = UART_DATA_8_BITS,
        .parity    = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_DEFAULT,
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
        .i2c_port = I2C_NUM_0,
        .sda_io_num = I2C_SDA_PIN,
        .scl_io_num = I2C_SCL_PIN,
        .clk_source = I2C_CLK_SRC_DEFAULT,
        .glitch_ignore_cnt = 7,
        .flags.enable_internal_pullup = true,
    };
    ESP_ERROR_CHECK(i2c_new_master_bus(&bus_config, &s_i2c_bus_handle));

    i2c_device_config_t dev_cfg_left = {
        .dev_addr_length = I2C_ADDR_BIT_LEN_7,
        .device_address = INA219_ADDR_LEFT,
        .scl_speed_hz = I2C_FREQ_HZ,
    };
    i2c_device_config_t dev_cfg_right = {
        .dev_addr_length = I2C_ADDR_BIT_LEN_7,
        .device_address = INA219_ADDR_RIGHT,
        .scl_speed_hz = I2C_FREQ_HZ,
    };

    if (i2c_master_bus_add_device(s_i2c_bus_handle, &dev_cfg_left, &s_ina_dev_left) == ESP_OK) {
        s_is_left_ina_ready = (init_ina219_dev(s_ina_dev_left) == ESP_OK);
    }
    if (i2c_master_bus_add_device(s_i2c_bus_handle, &dev_cfg_right, &s_ina_dev_right) == ESP_OK) {
        s_is_right_ina_ready = (init_ina219_dev(s_ina_dev_right) == ESP_OK);
    }
}

static void init_led_strips(void) {
    led_strip_config_t strip_config = {
        .strip_gpio_num = DATA_PIN_1,
        .max_leds = NUM_LEDS,
        .led_model = LED_MODEL_WS2812,
    };

    led_strip_rmt_config_t rmt_config = {
        .resolution_hz = 10 * 1000 * 1000,
    };

    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &s_strip1));

    strip_config.strip_gpio_num = DATA_PIN_2;
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &s_strip2));

    clear_all_leds();
    flush_led_strips();
}

void app_main(void) {
    s_state_mutex = xSemaphoreCreateMutex();
    s_wroom_tx_mutex = xSemaphoreCreateMutex();

    gpio_config_t io_conf = {
        .pin_bit_mask = (1ULL << RELAY_PIN) | (1ULL << PROJECTOR_PIN),
        .mode = GPIO_MODE_OUTPUT,
        .pull_down_en = 0,
        .pull_up_en = 0,
    };
    gpio_config(&io_conf);
    gpio_set_level(RELAY_PIN, 1);
    gpio_set_level(PROJECTOR_PIN, 1);

    init_uarts();
    init_i2c_bus();
    init_led_strips();

    for (uint8_t i = 0; i < NUM_COLUMNS; i++) {
        s_column_state[i] = STATE_WAITING;
        s_column_next_drop[i] = millis() + (rand() % 1900 + 100);
    }

    read_battery_and_calculate_pct();
    update_power_relay_only();
    s_sleep_wake_timer = millis();

    ESP_LOGI(TAG, "🚀 ESP32-P4 Non-Zero 39B PLC Firmware Initialized! (Rail: %d)", MY_RAIL_SEQ);

    xTaskCreatePinnedToCore(comm_task, "comm_task", 4096, NULL, 5, NULL, 0);
    xTaskCreatePinnedToCore(presentation_task, "pres_task", 4096, NULL, 4, NULL, 1);
}