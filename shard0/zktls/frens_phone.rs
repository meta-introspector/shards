use tlsn_core::{Prover, ProverConfig};
use tokio::net::TcpStream;
use std::env;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        eprintln!("Usage: {} <solscan_token_url>", args[0]);
        eprintln!("Example: {} https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22", args[0]);
        std::process::exit(1);
    }
    
    let url = &args[1];
    
    // Extract token address from URL
    let token = url.split('/').last().unwrap_or("");
    
    println!("📞 Generating FRENS phone number from zkTLS proof...");
    println!("🔗 URL: {}", url);
    println!("🪙 Token: {}\n", token);
    
    // Generate zkTLS proof
    println!("🔐 Connecting to solscan.io via TLSNotary...");
    
    let config = ProverConfig::builder()
        .server_name("solscan.io")
        .build()?;
    
    let prover = Prover::new(config).await?;
    let stream = TcpStream::connect("solscan.io:443").await?;
    let (mut tls_conn, prover_fut) = prover.connect(stream).await?;
    
    let request = format!(
        "GET /token/{} HTTP/1.1\r\nHost: solscan.io\r\nConnection: close\r\n\r\n",
        token
    );
    
    tls_conn.write_all(request.as_bytes()).await?;
    
    let mut response = Vec::new();
    tls_conn.read_to_end(&mut response).await?;
    
    let prover = prover_fut.await?;
    let proof = prover.finalize().await?;
    
    println!("✅ zkTLS proof generated ({} bytes)\n", proof.data().len());
    
    // Convert token address to phone number
    let token_bytes = bs58::decode(token).into_vec()?;
    
    let mut phone_digits = String::new();
    for byte in token_bytes.iter().take(10) {
        phone_digits.push_str(&format!("{:02}", byte % 100));
    }
    
    let area_code = &phone_digits[0..3];
    let exchange = &phone_digits[3..6];
    let subscriber = &phone_digits[6..10];
    
    let phone_number = format!("+1-{}-{}-{}", area_code, exchange, subscriber);
    
    println!("📞 FRENS Phone Number (from token address):");
    println!("   {}\n", phone_number);
    
    let jinv_number = "+1-744-196-8840";
    println!("📞 j-Invariant Themed Number:");
    println!("   {} (744 = constant, 196884 = Moonshine)\n", jinv_number);
    
    let vanity = "1-744-FRENS-71";
    println!("📞 Vanity Number:");
    println!("   {} (1-744-373-6771)\n", vanity);
    
    // Save proof and phone mapping
    std::fs::write("frens_proof.tlsn", proof.data())?;
    std::fs::write("frens_phone.txt", format!(
        "Token: {}\nURL: {}\nPhone: {}\nj-Invariant: {}\nVanity: {}\n",
        token, url, phone_number, jinv_number, vanity
    ))?;
    
    println!("✅ Files saved:");
    println!("   frens_proof.tlsn - zkTLS proof");
    println!("   frens_phone.txt - Phone numbers\n");
    
    println!("🎉 Call {} to access FRENS BBS!", jinv_number);
    
    Ok(())
}
