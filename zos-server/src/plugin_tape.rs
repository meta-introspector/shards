// Plugin Tape System - Each plugin is a ZK-RDF compressed blob sharded across 71 nodes
// zos-server/src/plugin_tape.rs

use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};
use flate2::{write::GzEncoder, read::GzDecoder, Compression};
use std::io::{Write, Read};
use base64::{Engine as _, engine::general_purpose};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginTape {
    pub name: String,
    pub shards: Vec<TapeShard>,
    pub merkle_root: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TapeShard {
    pub id: u8,
    pub blob: Vec<u8>,
    pub hash: [u8; 32],
}

impl PluginTape {
    pub fn from_binary(name: String, binary: &[u8]) -> Self {
        let chunk_size = (binary.len() + 70) / 71;
        let mut shards = Vec::new();
        
        for i in 0..71 {
            let start = i * chunk_size;
            let end = (start + chunk_size).min(binary.len());

            // Handle case where we've already consumed all data
            let chunk = if start >= binary.len() {
                &[]
            } else {
                &binary[start..end]
            };
            
            // RDF triple
            let rdf = format!("shard:{} cicada:data \"{}\"", i, general_purpose::STANDARD.encode(chunk));
            
            // Compress
            let mut enc = GzEncoder::new(Vec::new(), Compression::best());
            enc.write_all(rdf.as_bytes()).unwrap();
            let blob = enc.finish().unwrap();
            
            // Hash
            let hash = Sha256::digest(&blob).into();
            
            shards.push(TapeShard { id: i as u8, blob, hash });
        }
        
        let merkle_root = Self::merkle_root(&shards);

        Self { name, shards, merkle_root }
    }
    
    pub fn reconstruct(&self) -> Vec<u8> {
        let mut binary = Vec::new();
        
        for shard in &self.shards {
            let mut dec = GzDecoder::new(&shard.blob[..]);
            let mut rdf = String::new();
            dec.read_to_string(&mut rdf).unwrap();
            
            // Extract base64 data
            let data = rdf.split('"').nth(1).unwrap();
            binary.extend(general_purpose::STANDARD.decode(data).unwrap());
        }
        
        binary
    }
    
    fn merkle_root(shards: &[TapeShard]) -> [u8; 32] {
        let mut hashes: Vec<[u8; 32]> = shards.iter().map(|s| s.hash).collect();
        
        while hashes.len() > 1 {
            hashes = hashes.chunks(2).map(|pair| {
                let mut h = Sha256::new();
                h.update(&pair[0]);
                if pair.len() > 1 { h.update(&pair[1]); }
                h.finalize().into()
            }).collect();
        }
        
        hashes[0]
    }
    
    pub fn save(&self, dir: &str) -> std::io::Result<()> {
        std::fs::create_dir_all(dir)?;
        
        for shard in &self.shards {
            std::fs::write(format!("{}/shard{:02}.tape", dir, shard.id), &shard.blob)?;
        }
        
        std::fs::write(
            format!("{}/manifest.json", dir),
            serde_json::to_string_pretty(self).unwrap()
        )?;
        
        Ok(())
    }
    
    pub fn load(dir: &str) -> std::io::Result<Self> {
        let manifest = std::fs::read_to_string(format!("{}/manifest.json", dir))?;
        let mut tape: Self = serde_json::from_str(&manifest)?;
        
        for shard in &mut tape.shards {
            shard.blob = std::fs::read(format!("{}/shard{:02}.tape", dir, shard.id))?;
        }
        
        Ok(tape)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_tape() {
        let data = b"Hello, Plugin!";
        let tape = PluginTape::from_binary("test".into(), data);
        assert_eq!(tape.shards.len(), 71);
        assert_eq!(&tape.reconstruct()[..], data);
    }
}
