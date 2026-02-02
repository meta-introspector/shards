/*
 * MAME Driver: Mother's Wisdom - Pick the Very Best One
 * The first game for all platforms
 * 
 * A children's rhyme becomes a Monster group puzzle game
 */

#include "emu.h"
#include "cpu/z80/z80.h"
#include "sound/ay8910.h"
#include "emupal.h"
#include "screen.h"
#include "speaker.h"

namespace {

class mothers_wisdom_state : public driver_device
{
public:
    mothers_wisdom_state(const machine_config &mconfig, device_type type, const char *tag)
        : driver_device(mconfig, type, tag)
        , m_maincpu(*this, "maincpu")
        , m_screen(*this, "screen")
    { }

    void mothers_wisdom(machine_config &config);

private:
    required_device<cpu_device> m_maincpu;
    required_device<screen_device> m_screen;

    uint32_t screen_update(screen_device &screen, bitmap_rgb32 &bitmap, const rectangle &cliprect);
    
    void main_map(address_map &map);
    void io_map(address_map &map);
    
    // Game state
    uint8_t m_current_prime = 0;
    uint8_t m_selected_prime = 17;  // Mother's choice
    uint16_t m_score = 0;
    
    static constexpr uint8_t PRIMES[15] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71};
    static constexpr const char* RHYME[15] = {
        "Eeny", "Meeny", "Miny", "Moe", "Catch",
        "A", "Tiger", "By", "Its", "Toe",
        "If", "It", "Hollers", "Let", "It"
    };
};

uint32_t mothers_wisdom_state::screen_update(screen_device &screen, bitmap_rgb32 &bitmap, const rectangle &cliprect)
{
    bitmap.fill(rgb_t::black(), cliprect);
    
    // Draw title
    // "MY MOTHER TAUGHT ME TO PICK THE VERY BEST ONE"
    
    // Draw current rhyme word
    // RHYME[m_current_prime]
    
    // Draw prime number
    // PRIMES[m_current_prime]
    
    // Draw shard
    // PRIMES[m_current_prime] % 71
    
    // Draw score
    // m_score
    
    // Highlight if selected == 17 (the best one)
    if (PRIMES[m_current_prime] == 17) {
        // Draw star, tiger emoji, "THE CUSP"
    }
    
    return 0;
}

void mothers_wisdom_state::main_map(address_map &map)
{
    map(0x0000, 0x3fff).rom();
    map(0x4000, 0x47ff).ram();
}

void mothers_wisdom_state::io_map(address_map &map)
{
    map.global_mask(0xff);
    map(0x00, 0x00).portr("IN0");
    map(0x01, 0x01).portr("IN1");
}

void mothers_wisdom_state::mothers_wisdom(machine_config &config)
{
    // CPU: Z80 @ 3.579545 MHz
    Z80(config, m_maincpu, 3.579545_MHz_XTAL);
    m_maincpu->set_addrmap(AS_PROGRAM, &mothers_wisdom_state::main_map);
    m_maincpu->set_addrmap(AS_IO, &mothers_wisdom_state::io_map);
    m_maincpu->set_vblank_int("screen", FUNC(mothers_wisdom_state::irq0_line_hold));

    // Video: 256x224 @ 60Hz
    SCREEN(config, m_screen, SCREEN_TYPE_RASTER);
    m_screen->set_refresh_hz(60);
    m_screen->set_vblank_time(ATTOSECONDS_IN_USEC(0));
    m_screen->set_size(256, 224);
    m_screen->set_visarea(0, 255, 0, 223);
    m_screen->set_screen_update(FUNC(mothers_wisdom_state::screen_update));

    // Sound: AY-3-8910
    SPEAKER(config, "mono").front_center();
    AY8910(config, "ay8910", 1.789772_MHz_XTAL).add_route(ALL_OUTPUTS, "mono", 0.30);
}

ROM_START( mothwis )
    ROM_REGION( 0x4000, "maincpu", 0 )
    ROM_LOAD( "mothwis.bin", 0x0000, 0x4000, CRC(17171717) SHA1(17171717171717171717171717171717) )
ROM_END

} // anonymous namespace

// Game driver
GAME( 2026, mothwis, 0, mothers_wisdom, mothers_wisdom, mothers_wisdom_state, empty_init, ROT0, "SOLFUNMEME", "Mother's Wisdom - Pick the Very Best One", MACHINE_SUPPORTS_SAVE )
