// FRACTRAN macro defines shard structure
// No hardcoded values - all from macro expansion

macro_rules! fractran_shard_structure {
    ($primes:expr) => {
        #[derive(Debug, Clone)]
        struct ShardStructure {
            primes: [u64; 4],
        }
        
        impl ShardStructure {
            fn new() -> Self {
                Self { primes: $primes }
            }
            
            fn dirname_mod(&self) -> u64 { self.primes[0] }
            fn subdir_mod(&self) -> u64 { self.primes[1] }
            fn filename_mod(&self) -> u64 { self.primes[2] }
            fn ext_mod(&self) -> u64 { self.primes[3] }
        }
    };
}

// Memory-mapped shard structure
#[derive(Debug, Clone)]
pub struct MemoryShard {
    pub dirname_shard: u64,
    pub subdir_shards: Vec<u64>,
    pub filename_shard: u64,
    pub ext_shard: u64,
}

impl MemoryShard {
    pub fn new(
        dirname_shard: u64,
        subdir_shards: Vec<u64>,
        filename_shard: u64,
        ext_shard: u64,
    ) -> Self {
        Self {
            dirname_shard,
            subdir_shards,
            filename_shard,
            ext_shard,
        }
    }
    
    // Map to FRACTRAN structure
    pub fn to_fractran_tuple(&self) -> (u64, Vec<u64>, u64, u64) {
        (
            self.dirname_shard,
            self.subdir_shards.clone(),
            self.filename_shard,
            self.ext_shard,
        )
    }
}

// Export macro
pub use fractran_shard_structure;
