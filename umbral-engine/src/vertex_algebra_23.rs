// 23-Vertex Monster Algebra - Complete Operator System
// Indexed by first 23 primes, capped at 71

use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum VertexOp {
    // Baseline SK combinators (8)
    S = 2,   // Substitution / interaction
    K = 3,   // Erasure / projection
    I = 5,   // Identity
    Y = 7,   // Fixpoint / recursion
    B = 11,  // Composition
    C = 13,  // Argument symmetry
    W = 17,  // Duplication
    T = 19,  // Time / trace / tick
    
    // Control & evaluation order (5)
    A = 23,  // Application (explicit apply node)
    E = 29,  // Evaluation / force (strictness)
    L = 31,  // Lambda abstraction marker
    R = 37,  // Return / reification
    F = 41,  // Failure / zero morphism
    
    // Reflection & self-inspection (4)
    Q = 43,  // Quote (code as data)
    U = 47,  // Unquote / eval
    H = 53,  // Hash / fingerprint
    M = 59,  // Mirror (swap code ↔ state)
    
    // Arithmetic & FRACTRAN-native (3)
    P = 61,  // Prime inject
    D = 67,  // Divide / cancel
    N = 71,  // Normalize (canonical factor form)
    
    // Geometry / Monster-facing probes (3, derived mod 71)
    G = 71,  // Group action (apply automorphism)
    J = 71,  // j-invariant / moonshine probe
    Z = 71,  // Zero / cusp / termination witness
}

impl VertexOp {
    pub fn from_prime(p: u8) -> Option<Self> {
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
            37 => Some(Self::R),
            41 => Some(Self::F),
            43 => Some(Self::Q),
            47 => Some(Self::U),
            53 => Some(Self::H),
            59 => Some(Self::M),
            61 => Some(Self::P),
            67 => Some(Self::D),
            71 => Some(Self::N),
            _ => None,
        }
    }
    
    pub fn to_prime(self) -> u8 {
        self as u8
    }
    
    pub fn category(self) -> &'static str {
        match self {
            Self::S | Self::K | Self::I | Self::Y | Self::B | Self::C | Self::W | Self::T => "baseline",
            Self::A | Self::E | Self::L | Self::R | Self::F => "control",
            Self::Q | Self::U | Self::H | Self::M => "reflection",
            Self::P | Self::D | Self::N => "arithmetic",
            Self::G | Self::J | Self::Z => "geometry",
        }
    }
}

// FRACTRAN program for 23-vertex algebra
pub fn vertex_fractran_program() -> Vec<(u64, u64)> {
    vec![
        // Baseline transformations
        (2, 1),   // S: inject
        (3, 2),   // K: S → K
        (5, 3),   // I: K → I
        (7, 5),   // Y: I → Y
        (11, 7),  // B: Y → B
        (13, 11), // C: B → C
        (17, 13), // W: C → W
        (19, 17), // T: W → T
        
        // Control layer
        (23, 19), // A: T → A
        (29, 23), // E: A → E
        (31, 29), // L: E → L
        (37, 31), // R: L → R (symmetry breakpoint)
        (41, 37), // F: R → F
        
        // Reflection layer
        (43, 41), // Q: F → Q
        (47, 43), // U: Q → U
        (53, 47), // H: U → H
        (59, 53), // M: H → M
        
        // Arithmetic layer
        (61, 59), // P: M → P
        (67, 61), // D: P → D
        (71, 67), // N: D → N (Monster cap)
        
        // Geometry fold (mod 71)
        (1, 71),  // N → 1 (cycle complete)
    ]
}

// Operator fusion rules (VOA-style OPE table)
pub fn fuse(op1: VertexOp, op2: VertexOp) -> VertexOp {
    let p1 = op1.to_prime() as u64;
    let p2 = op2.to_prime() as u64;
    let product = (p1 * p2) % 71;
    
    VertexOp::from_prime(product as u8).unwrap_or(VertexOp::N)
}

// Self-measuring recursion: Y + Q + H + T
pub fn self_measure(input: u64) -> (VertexOp, u64) {
    let ops = [VertexOp::Y, VertexOp::Q, VertexOp::H, VertexOp::T];
    let mut state = input;
    
    for op in ops {
        state = (state * op.to_prime() as u64) % 71;
    }
    
    (VertexOp::from_prime((state % 71) as u8).unwrap_or(VertexOp::N), state)
}

// Moonshine sampling: J + G
pub fn moonshine_sample(j_invariant: u64) -> VertexOp {
    let g_action = (j_invariant * VertexOp::G.to_prime() as u64) % 71;
    let j_probe = (g_action * VertexOp::J.to_prime() as u64) % 71;
    
    VertexOp::from_prime((j_probe % 71) as u8).unwrap_or(VertexOp::Z)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_23_operators() {
        assert_eq!(VertexOp::S.to_prime(), 2);
        assert_eq!(VertexOp::N.to_prime(), 71);
        assert_eq!(VertexOp::from_prime(47), Some(VertexOp::U));
    }
    
    #[test]
    fn test_fusion() {
        let result = fuse(VertexOp::S, VertexOp::K);
        assert_eq!(result.to_prime(), 6 % 71);
    }
    
    #[test]
    fn test_self_measure() {
        let (op, state) = self_measure(2);
        assert!(state < 71);
    }
}
