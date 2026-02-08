use sha2::{Sha256, Digest};
use std::net::IpAddr;

// Supersingular primes
const PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

pub struct Shard {
    pub ip_shard: u64,      // IP mod 71
    pub port_shard: u64,    // Port mod 59
    pub packet_shard: u64,  // Packet hash mod 47
    pub byte_shard: u64,    // Byte offset mod 23
}

pub fn shard_ip(ip: &IpAddr) -> u64 {
    match ip {
        IpAddr::V4(addr) => {
            let octets = addr.octets();
            let ip_num = u32::from_be_bytes(octets) as u64;
            ip_num % 71
        }
        IpAddr::V6(addr) => {
            let segments = addr.segments();
            let ip_num = segments.iter().fold(0u64, |acc, &s| acc.wrapping_add(s as u64));
            ip_num % 71
        }
    }
}

pub fn shard_port(port: u16) -> u64 {
    (port as u64) % 59
}

pub fn shard_packet(data: &[u8]) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let hash = hasher.finalize();
    let hash_num = u64::from_be_bytes([
        hash[0], hash[1], hash[2], hash[3],
        hash[4], hash[5], hash[6], hash[7],
    ]);
    hash_num % 47
}

pub fn shard_byte_offset(offset: usize) -> u64 {
    (offset as u64) % 23
}

pub fn shard_all(ip: &IpAddr, port: u16, packet: &[u8], offset: usize) -> Shard {
    Shard {
        ip_shard: shard_ip(ip),
        port_shard: shard_port(port),
        packet_shard: shard_packet(packet),
        byte_shard: shard_byte_offset(offset),
    }
}
