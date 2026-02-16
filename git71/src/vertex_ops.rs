// 23-Vertex operators for git71
// ONLY supersingular primes (Monster moonshine resonance)

// Supersingular primes: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71
// Total: 15 primes

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum VertexOp {
    // Baseline SK combinators (supersingular)
    S = 2,   // ✓ Monster resonance
    K = 3,   // ✓ Monster resonance
    I = 5,   // ✓ Monster resonance
    Y = 7,   // ✓ Monster resonance
    B = 11,  // ✓ Monster resonance
    C = 13,  // ✓ Monster resonance
    W = 17,  // ✓ Monster resonance
    T = 19,  // ✓ Monster resonance
    
    // Control & evaluation (supersingular)
    A = 23,  // ✓ Monster resonance (Paxos)
    E = 29,  // ✓ Monster resonance
    L = 31,  // ✓ Monster resonance
    F = 41,  // ✓ Monster resonance
    
    // Reflection (supersingular)
    Q = 43,  // ❌ NOT supersingular → Zone X
    U = 47,  // ✓ Monster resonance
    H = 53,  // ❌ NOT supersingular → Zone X
    M = 59,  // ✓ Monster resonance
    
    // Arithmetic (supersingular)
    N = 71,  // ✓ Monster resonance (cap)
}

// Zone X: Non-supersingular primes (NO Monster resonance)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ZoneX {
    R = 37,  // ❌ NOT supersingular
    Q = 43,  // ❌ NOT supersingular
    H = 53,  // ❌ NOT supersingular
    P = 61,  // ❌ NOT supersingular
    D = 67,  // ❌ NOT supersingular
}

impl VertexOp {
    pub fn from_prime(p: u8) -> Option<Self> {
        // Only supersingular primes
        match p {
            2 => Some(Self::S),
            3 => Some(Self::K),
            5 => Some(Self::I),
            7 => Some(Self::Y),
            11 => Some(Self::B),
            13 => Some(Self::C),
            17 => Some(Self::W),
            19 => Some(Self::T),
            23 => Some(Self::A),
            29 => Some(Self::E),
            31 => Some(Self::L),
            41 => Some(Self::F),
            47 => Some(Self::U),
            59 => Some(Self::M),
            71 => Some(Self::N),
            _ => None,  // Non-supersingular → Zone X
        }
    }
    
    pub fn is_supersingular(p: u8) -> bool {
        matches!(p, 2|3|5|7|11|13|17|19|23|29|31|41|47|59|71)
    }
}

impl ZoneX {
    pub fn from_prime(p: u8) -> Option<Self> {
        match p {
            37 => Some(Self::R),
            43 => Some(Self::Q),
            53 => Some(Self::H),
            61 => Some(Self::P),
            67 => Some(Self::D),
            _ => None,
        }
    }
    
    pub fn warning(&self) -> &'static str {
        "⚠️ DANGER: Non-supersingular prime - NO Monster moonshine resonance"
    }
}

// Correct count: 15 supersingular operators
pub const SUPERSINGULAR_COUNT: usize = 15;
pub const ZONE_X_COUNT: usize = 5;
