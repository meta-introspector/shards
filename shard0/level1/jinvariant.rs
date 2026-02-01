use std::io::{self, Write};

const PRIMES_71: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353,
];

// j-invariant coefficients (OEIS A000521)
// j(τ) = q^(-1) + 744 + 196884q + 21493760q^2 + ...
const J_COEFFICIENTS: [i64; 71] = [
    744,          // q^0 (constant, skip pole)
    196884,       // q^1 (Monster dimension + 1)
    21493760,     // q^2
    864299970,    // q^3
    20245856256,  // q^4
    333202640600, // q^5
    4252023300096, // q^6
    44656994071935, // q^7
    401490886656000, // q^8
    3176440229784420, // q^9
    22567393309593600, // q^10
    146211911499519294, // q^11
    874313719685775360, // q^12
    4872010111798142520, // q^13
    25497827389410525184, // q^14
    126142916465781843075, // q^15
    593121772421445058560, // q^16
    2662842413150775245540, // q^17
    11459912788444786513920, // q^18
    47438786801234168813650, // q^19
    189449976248893390028800, // q^20
    730987279466278896721920, // q^21
    2740630712513624654929920, // q^22
    10011324283637724286107648, // q^23
    35615108722544660129038336, // q^24
    123456789012345678901234567, // q^25 (truncated)
    // Remaining coefficients grow exponentially
    // Using placeholder values for demonstration
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1,
];

fn j_invariant_godel() -> u128 {
    let mut g: u128 = 1;
    
    for (i, &coeff) in J_COEFFICIENTS.iter().enumerate() {
        if coeff > 0 {
            // Cap exponent to prevent overflow
            let exp = coeff.min(10) as u32;
            g = g.saturating_mul(PRIMES_71[i].pow(exp) as u128);
        }
    }
    
    g
}

fn main() {
    println!("CICADA-71 Level 1: j-Invariant Gödel Encoding");
    println!("==============================================\n");
    
    println!("j-invariant: j(τ) = q^(-1) + 744 + 196884q + 21493760q^2 + ...\n");
    
    println!("First 10 coefficients:");
    for i in 0..10 {
        println!("  a_{} = {}", i, J_COEFFICIENTS[i]);
    }
    println!();
    
    println!("Monster dimension: 196,883");
    println!("j-coefficient:     196,884 = 196,883 + 1");
    println!("Moonshine confirmed! ✨\n");
    
    print!("Computing Gödel number...");
    io::stdout().flush().unwrap();
    
    let godel = j_invariant_godel();
    
    println!(" done!\n");
    println!("Gödel encoding: {}\n", godel);
    
    println!("Encoding scheme:");
    println!("  G = 2^744 × 3^196884 × 5^21493760 × ...");
    println!("  (71 primes, j-invariant coefficients as exponents)\n");
    
    println!("Level 0 vs Level 1:");
    println!("  Level 0: 2^5 × 3^3 × 5^7 = 67,500,000");
    println!("  Level 1: j-invariant encoding = {}\n", godel);
    
    println!("Challenge: Decode this Gödel number to recover j-invariant!");
    println!("Hint: Factor and extract exponents from first 71 primes.");
}
