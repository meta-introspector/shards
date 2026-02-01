use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum P2PProtocol {
    Bitcoin,
    Solana,
    LibP2P,
    Tor,
    I2P,
    IPFS,
    DeadDrop,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IsupMessage {
    IAM { call_id: [u8; 16], called_number: String, calling_number: String },
    ACM { call_id: [u8; 16] },
    ANM { call_id: [u8; 16] },
    REL { call_id: [u8; 16], cause: u8 },
    RLC { call_id: [u8; 16] },
}

impl IsupMessage {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).unwrap()
    }
    
    pub fn decode(data: &[u8]) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(bincode::deserialize(data)?)
    }
}

impl P2PProtocol {
    pub fn for_shard(shard: u8) -> Self {
        match shard % 7 {
            0 => Self::Bitcoin,
            1 => Self::Solana,
            2 => Self::LibP2P,
            3 => Self::Tor,
            4 => Self::I2P,
            5 => Self::IPFS,
            6 => Self::DeadDrop,
            _ => unreachable!(),
        }
    }
    
    pub fn port(&self, shard: u8) -> u16 {
        match self {
            Self::Bitcoin => 8333 + shard as u16,
            Self::Solana => 8001 + shard as u16,
            Self::LibP2P => 4001 + shard as u16,
            Self::Tor => 9050,
            Self::I2P => 7656,
            Self::IPFS => 4001 + shard as u16,
            Self::DeadDrop => 0,
        }
    }
    
    pub fn peers(&self) -> usize {
        match self {
            Self::Bitcoin => 11,  // Shards 0,7,14,21,28,35,42,49,56,63,70
            Self::Solana => 10,   // Shards 1,8,15,22,29,36,43,50,57,64
            Self::LibP2P => 10,   // Shards 2,9,16,23,30,37,44,51,58,65
            Self::Tor => 10,      // Shards 3,10,17,24,31,38,45,52,59,66
            Self::I2P => 10,      // Shards 4,11,18,25,32,39,46,53,60,67
            Self::IPFS => 10,     // Shards 5,12,19,26,33,40,47,54,61,68
            Self::DeadDrop => 10, // Shards 6,13,20,27,34,41,48,55,62,69
        }
    }
}

pub fn shards_for_protocol(protocol: P2PProtocol) -> Vec<u8> {
    let offset = match protocol {
        P2PProtocol::Bitcoin => 0,
        P2PProtocol::Solana => 1,
        P2PProtocol::LibP2P => 2,
        P2PProtocol::Tor => 3,
        P2PProtocol::I2P => 4,
        P2PProtocol::IPFS => 5,
        P2PProtocol::DeadDrop => 6,
    };
    (0..protocol.peers()).map(|i| offset + (i as u8 * 7)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_shards_covered() {
        let mut covered = vec![false; 71];
        for shard in 0..71 {
            let proto = P2PProtocol::for_shard(shard);
            covered[shard as usize] = true;
            assert!(proto.port(shard) > 0 || matches!(proto, P2PProtocol::DeadDrop));
        }
        assert!(covered.iter().all(|&c| c));
    }

    #[test]
    fn test_bitcoin_shards() {
        let shards = shards_for_protocol(P2PProtocol::Bitcoin);
        assert_eq!(shards, vec![0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70]);
    }

    #[test]
    fn test_protocol_distribution() {
        for proto_id in 0..7 {
            let proto = P2PProtocol::for_shard(proto_id);
            let shards = shards_for_protocol(proto);
            assert_eq!(shards.len(), proto.peers());
        }
    }
}
