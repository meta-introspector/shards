mod shard;

use lava_torrent::torrent::v1::Torrent;
use reqwest;
use shard::*;
use std::fs::File;
use std::io::Write;
use std::net::IpAddr;
use tokio;

const OSM_TORRENT_URL: &str = "https://planet.openstreetmap.org/pbf/planet-latest.osm.pbf.torrent";
const WIKIPEDIA_TORRENT_URL: &str = "https://academictorrents.com/download/0852ef544a4694995fcbef7132477c688ded7d9a.torrent";

async fn download_and_shard(url: &str, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Downloading {} ===", name);
    
    let response = reqwest::get(url).await?;
    let bytes = response.bytes().await?;
    
    let output_file = format!("{}.torrent", name);
    let mut file = File::create(&output_file)?;
    file.write_all(&bytes)?;
    println!("Downloaded {} bytes to {}", bytes.len(), output_file);
    
    // Parse torrent
    let torrent = Torrent::read_from_bytes(&bytes)?;
    println!("Name: {}", torrent.name);
    
    // Shard tracker IPs
    if let Some(announce_list) = &torrent.announce_list {
        println!("\nSharding tracker IPs:");
        for (i, tier) in announce_list.iter().enumerate() {
            for tracker_url in tier {
                if let Ok(parsed) = url::Url::parse(tracker_url) {
                    if let Some(host) = parsed.host_str() {
                        if let Ok(ip) = host.parse::<IpAddr>() {
                            let shard = shard_ip(&ip);
                            println!("Tracker {}: {} → shard {}", i, ip, shard);
                        }
                    }
                }
            }
        }
    }
    
    // Shard torrent metadata
    let meta_shard = shard_packet(&bytes);
    println!("Metadata shard (mod 47): {}", meta_shard);
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Download and shard OSM planet
    download_and_shard(OSM_TORRENT_URL, "osm-planet").await?;
    
    // Download and shard Wikipedia
    download_and_shard(WIKIPEDIA_TORRENT_URL, "wikipedia").await?;
    
    println!("\n=== Ready to join swarms and shard packets ===");
    Ok(())
}

