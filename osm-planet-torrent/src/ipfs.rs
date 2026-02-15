use ipfs_api_backend_hyper::{IpfsApi, IpfsClient, TryFromUri};
use std::io::Cursor;

pub struct IpfsStore {
    client: IpfsClient,
}

impl IpfsStore {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let client = IpfsClient::from_str("http://127.0.0.1:5001")?;
        Ok(Self { client })
    }
    
    pub async fn add_shard(&self, shard_id: u64, data: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
        let cursor = Cursor::new(data);
        let response = self.client.add(cursor).await?;
        println!("Shard {} → IPFS: {}", shard_id, response.hash);
        Ok(response.hash)
    }
}
