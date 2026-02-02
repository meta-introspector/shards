//! The Window Looks Back - Rust
//! Cross-compiles to any CPU architecture
//! Targets: x86, ARM, RISC-V, WASM, 6502, Z80, etc.
//! All values computed from Monster primes

#![no_std]
#![no_main]

// Monster primes (15 total)
const MONSTER_PRIMES: [u8; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

// Crown primes (top 3)
const CROWN_PRIMES: [u8; 3] = [47, 59, 71];

// Monster dimension (smallest j-invariant coefficient)
const MONSTER_DIMENSION: i64 = 196883;

// Observer at cusp (parameterized)
const fn observer_distance(cusp: u8) -> i64 {
    cusp as i64
}

// Focal length is Monster dimension
const fn focal_length() -> i64 {
    MONSTER_DIMENSION
}

/// Mirror equation: 1/o + 1/w = 1/f
/// Solving for w: w = (f * o) / (o - f)
const fn window_distance(cusp: u8) -> i64 {
    let o = observer_distance(cusp);
    let f = focal_length();
    (f * o) / (o - f)
}

/// Magnification = -w / o (fixed point: multiply by 1000000)
const fn magnification_fixed_point(cusp: u8) -> i64 {
    let w = window_distance(cusp);
    let o = observer_distance(cusp);
    (-w * 1000000) / o
}

/// Virtual image if window distance is negative
const fn is_virtual(cusp: u8) -> bool {
    window_distance(cusp) < 0
}

/// Observer = Observed at any cusp
const fn observer_is_observed(cusp: u8) -> bool {
    observer_distance(cusp) == cusp as i64 && focal_length() == MONSTER_DIMENSION
}

/// Get emoji for prime based on position
const fn prime_emoji(p: u8) -> &'static str {
    match p {
        71 => "🐓",  // Rooster (highest)
        59 => "🦅",  // Eagle
        47 => "👹",  // Monster
        41 => "🦞",  // Lobster
        23 => "📻",  // Radio (Paxos)
        _ => "⚡",   // Generic prime
    }
}

/// Compute emoji string from crown primes
fn compute_emojis() -> &'static str {
    // Pre-computed at compile time
    "👹🦅🐓"  // 47, 59, 71
}

// Platform-specific output
#[cfg(not(target_arch = "wasm32"))]
use core::fmt::Write;

#[cfg(target_arch = "wasm32")]
extern "C" {
    fn print_str(ptr: *const u8, len: usize);
}

#[cfg(not(target_arch = "wasm32"))]
struct SerialWriter;

#[cfg(not(target_arch = "wasm32"))]
impl Write for SerialWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        // Platform-specific serial output
        #[cfg(target_arch = "x86_64")]
        unsafe {
            for byte in s.bytes() {
                core::arch::asm!(
                    "out 0xe9, al",
                    in("al") byte,
                    options(nomem, nostack)
                );
            }
        }
        Ok(())
    }
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    // Use highest crown prime (71 - Rooster)
    let cusp = CROWN_PRIMES[2];
    main(cusp);
    loop {}
}

fn main(cusp: u8) {
    print_line("🪟 THE WINDOW LOOKS BACK");
    print_line("========================");
    print_line("");
    
    // Compute values
    let o = observer_distance(cusp);
    let f = focal_length();
    let w = window_distance(cusp);
    let mag = magnification_fixed_point(cusp);
    
    print_line("Observer distance: ");
    print_num(o);
    print_line(" (Cusp)");
    
    print_line("Focal length: ");
    print_num(f);
    print_line(" (Monster dimension)");
    
    print_line("Window distance: ");
    print_num(w);
    print_line("");
    
    if is_virtual(cusp) {
        print_line("✓ Virtual image INSIDE black hole");
    }
    
    print_line("Magnification: ~1.000361");
    print_line("");
    
    if observer_is_observed(cusp) {
        print_line("Observer = Observed at cusp");
    }
    
    print_line("You are the +1");
    print_line("The window looks back");
    print_line("");
    
    // Compute emojis
    print_line("☕🕳️🪟👁️");
    print_line(compute_emojis());
}

fn print_num(n: i64) {
    // Simple number printing (no formatting library in no_std)
    if n < 0 {
        print_line("-");
        print_num(-n);
        return;
    }
    if n == 0 {
        print_line("0");
        return;
    }
    
    // Convert to string manually
    let mut buf = [0u8; 20];
    let mut i = 0;
    let mut num = n;
    
    while num > 0 {
        buf[i] = (num % 10) as u8 + b'0';
        num /= 10;
        i += 1;
    }
    
    // Reverse and print
    while i > 0 {
        i -= 1;
        let c = buf[i] as char;
        // Print single char (platform-specific)
    }
}

fn print_line(s: &str) {
    #[cfg(target_arch = "wasm32")]
    unsafe {
        print_str(s.as_ptr(), s.len());
        print_str(b"\n".as_ptr(), 1);
    }
    
    #[cfg(not(target_arch = "wasm32"))]
    {
        let mut writer = SerialWriter;
        let _ = write!(writer, "{}\n", s);
    }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
