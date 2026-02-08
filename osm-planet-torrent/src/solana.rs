use solana_client::rpc_client::RpcClient;
use solana_sdk::{
    signature::{Keypair, Signer, read_keypair_file},
    transaction::Transaction,
    system_instruction,
    commitment_config::CommitmentConfig,
};
use sha2::{Sha256, Digest};
use std::env;
use std::path::Path;

pub struct SolanaWitness {
    client: RpcClient,
    keypair: Keypair,
    shard: u64,
}

impl SolanaWitness {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // Read keypair from sops-managed secret
        let keypair_path = env::var("SOLANA_KEYPAIR_PATH")?;
        let keypair = read_keypair_file(Path::new(&keypair_path))?;
        
        // Security shard from environment
        let shard: u64 = env::var("SECURITY_SHARD")?.parse()?;
        
        // Testnet RPC
        let client = RpcClient::new_with_commitment(
            "https://api.testnet.solana.com".to_string(),
            CommitmentConfig::confirmed(),
        );
        
        Ok(Self { client, keypair, shard })
    }
    
    pub async fn write_signature(&self, shard_id: u64, ipfs_hash: &str) -> Result<String, Box<dyn std::error::Error>> {
        // Verify we're in security shard 23
        if self.shard != 23 {
            return Err("Must execute in security shard 23".into());
        }
        
        // Create signature: SHA256(shard_id || ipfs_hash)
        let mut hasher = Sha256::new();
        hasher.update(shard_id.to_le_bytes());
        hasher.update(ipfs_hash.as_bytes());
        let sig_hash = hasher.finalize();
        
        // Get recent blockhash
        let recent_blockhash = self.client.get_latest_blockhash()?;
        
        // Create memo instruction with signature
        let memo_data = format!("shard:{} ipfs:{} sig:{:x}", shard_id, ipfs_hash, sig_hash);
        let memo_ix = spl_memo::build_memo(memo_data.as_bytes(), &[&self.keypair.pubkey()]);
        
        // Build and send transaction
        let tx = Transaction::new_signed_with_payer(
            &[memo_ix],
            Some(&self.keypair.pubkey()),
            &[&self.keypair],
            recent_blockhash,
        );
        
        let signature = self.client.send_and_confirm_transaction(&tx)?;
        
        println!("Shard {} witness written to Solana testnet", shard_id);
        println!("Transaction: {}", signature);
        println!("IPFS: {}", ipfs_hash);
        
        Ok(signature.to_string())
    }
}
