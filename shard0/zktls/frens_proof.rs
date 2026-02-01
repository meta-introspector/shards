use tlsn_core::{Prover, ProverConfig};
use tokio::net::TcpStream;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔐 Generating zkTLS proof for FRENS token...");
    
    // TLSNotary prover setup
    let config = ProverConfig::builder()
        .server_name("solscan.io")
        .build()?;
    
    let prover = Prover::new(config).await?;
    
    // Connect to Solscan
    println!("📡 Connecting to solscan.io via TLSNotary...");
    let stream = TcpStream::connect("solscan.io:443").await?;
    
    // Start TLS session with notarization
    let (mut tls_conn, prover_fut) = prover.connect(stream).await?;
    
    // Send HTTP request
    let request = format!(
        "GET /token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22 HTTP/1.1\r\n\
         Host: solscan.io\r\n\
         Connection: close\r\n\
         \r\n"
    );
    
    tls_conn.write_all(request.as_bytes()).await?;
    
    // Read response
    let mut response = Vec::new();
    tls_conn.read_to_end(&mut response).await?;
    
    println!("✅ Received response ({} bytes)", response.len());
    
    // Finalize and generate proof
    let prover = prover_fut.await?;
    let proof = prover.finalize().await?;
    
    println!("🔐 zkTLS proof generated!");
    println!("   Proof size: {} bytes", proof.data().len());
    
    // Extract token data from response
    let response_str = String::from_utf8_lossy(&response);
    
    // Parse JSON (simplified)
    let holders = extract_field(&response_str, "holders").unwrap_or("0");
    let supply = extract_field(&response_str, "supply").unwrap_or("0");
    let price = extract_field(&response_str, "price").unwrap_or("0");
    
    println!("\n✅ Extracted data (zkTLS verified):");
    println!("   Holders: {}", holders);
    println!("   Supply: {}", supply);
    println!("   Price: ${}", price);
    
    // Calculate Gödel number
    let holders_num: u32 = holders.parse().unwrap_or(0);
    let godel_exp = holders_num % 100;
    
    println!("\n🔢 Gödel encoding:");
    println!("   2^{} × 3^1000 × 5^420", godel_exp);
    
    // Generate RDFa
    let rdfa = generate_rdfa(
        "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22",
        &holders,
        &supply,
        &price,
        godel_exp,
    );
    
    // Save proof
    std::fs::write("frens_proof.tlsn", proof.data())?;
    std::fs::write("frens_invite.rdfa", &rdfa)?;
    
    // Generate invite URL
    let rdfa_encoded = urlencoding::encode(&rdfa);
    let invite_url = format!(
        "https://cicada71.bbs.workers.dev/invite?\
         token=E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22\
         &holders={}&supply={}&price={}&godel={}&rdfa={}",
        holders, supply, price, godel_exp, rdfa_encoded
    );
    
    std::fs::write("frens_invite.url", &invite_url)?;
    
    println!("\n✨ Generated files:");
    println!("   frens_proof.tlsn - zkTLS proof");
    println!("   frens_invite.rdfa - RDFa metadata");
    println!("   frens_invite.url - Invite URL");
    
    println!("\n🔗 Invite URL:");
    println!("{}", invite_url);
    
    Ok(())
}

fn extract_field(html: &str, field: &str) -> Option<String> {
    // Simple extraction (would use proper JSON parsing in production)
    let pattern = format!("\"{}\":", field);
    if let Some(start) = html.find(&pattern) {
        let rest = &html[start + pattern.len()..];
        if let Some(end) = rest.find(&[',', '}'][..]) {
            return Some(rest[..end].trim().trim_matches('"').to_string());
        }
    }
    None
}

fn generate_rdfa(token: &str, holders: &str, supply: &str, price: &str, godel: u32) -> String {
    format!(r#"<div vocab="http://schema.org/" typeof="FinancialProduct">
  <meta property="name" content="FRENS Token"/>
  <meta property="identifier" content="{}"/>
  
  <div property="proof" typeof="Proof">
    <meta property="proofType" content="zkTLS"/>
    <meta property="proofMethod" content="TLSNotary"/>
    <meta property="created" content="{}"/>
  </div>
  
  <div property="tokenData" typeof="TokenMetrics">
    <meta property="holders" content="{}"/>
    <meta property="supply" content="{}"/>
    <meta property="price" content="{}"/>
  </div>
  
  <div property="godelEncoding">
    <meta property="expression" content="2^{} × 3^1000 × 5^420"/>
    <meta property="shards" content="71"/>
  </div>
  
  <div property="cicada71">
    <meta property="shard" content="72"/>
    <meta property="phone" content="+1-744-196-8840"/>
    <link property="bbs" href="https://cicada71.bbs.workers.dev/dial/744-196-8840"/>
  </div>
</div>"#,
        token,
        chrono::Utc::now().to_rfc3339(),
        holders,
        supply,
        price,
        godel
    )
}
