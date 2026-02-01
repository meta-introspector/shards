use std::io::{self, Write};

struct VirtualPhone {
    dialed: Vec<String>,
}

impl VirtualPhone {
    fn new() -> Self {
        VirtualPhone { dialed: vec![] }
    }
    
    fn dial(&mut self, digits: &str) -> Result<String, String> {
        if digits.len() > 15 {
            return Err(format!("❌ Number too large: {} digits (max 15)", digits.len()));
        }
        
        self.dialed.push(digits.to_string());
        
        match digits {
            "744" => Ok("✅ Constant term accepted. j(τ) = q^(-1) + 744 + ...".to_string()),
            "196883" => Ok("✅ Monster dimension recognized!".to_string()),
            "196884" => Ok("✅ Moonshine coefficient! (196883 + 1)".to_string()),
            "493760" => Ok("✅ q^2 coefficient (mod 10^6)".to_string()),
            "#" => Ok("✅ Sequence complete!".to_string()),
            _ => Ok(format!("📞 Dialing {}...", digits)),
        }
    }
    
    fn send_fax(&self, to: &str, content: &str) -> Result<(), String> {
        println!("\n📠 FAX TRANSMISSION");
        println!("==================");
        println!("TO:   {}", to);
        println!("FROM: CICADA-71 Agent");
        println!("\n{}", content);
        println!("==================");
        println!("✅ Fax sent successfully!\n");
        Ok(())
    }
}

fn main() {
    println!("📞 CICADA-71 Level 5: Dial the j-Invariant");
    println!("===========================================\n");
    
    let mut phone = VirtualPhone::new();
    
    println!("Challenge: Dial the j-invariant");
    println!("j(τ) = q^(-1) + 744 + 196884q + 21493760q^2 + ...\n");
    
    println!("Problem: Phone numbers max at 15 digits");
    println!("Solution: Dial coefficients sequentially\n");
    
    // Dial sequence
    println!("Dialing sequence:\n");
    
    match phone.dial("744") {
        Ok(msg) => println!("{}", msg),
        Err(e) => println!("{}", e),
    }
    std::thread::sleep(std::time::Duration::from_millis(500));
    
    match phone.dial("196884") {
        Ok(msg) => println!("{}", msg),
        Err(e) => println!("{}", e),
    }
    std::thread::sleep(std::time::Duration::from_millis(500));
    
    match phone.dial("493760") {
        Ok(msg) => println!("{}", msg),
        Err(e) => println!("{}", e),
    }
    std::thread::sleep(std::time::Duration::from_millis(500));
    
    match phone.dial("#") {
        Ok(msg) => println!("{}", msg),
        Err(e) => println!("{}", e),
    }
    
    println!("\n🎉 j-invariant dialed successfully!");
    println!("Dialed: {:?}\n", phone.dialed);
    
    // Send fax
    let fax_content = r#"j(τ) = q^(-1) + 744 + 196884q + 21493760q^2 + ...

Monster dimension: 196,883
Moonshine coefficient: 196,884 = 196,883 + 1

Gödel encoding:
G = 2^744 × 3^196884 × 5^21493760 × ...

The infinite cannot be dialed, only approximated.
The eternal cannot be faxed, only referenced.

Signature: CICADA-71 Agent
Timestamp: [UNIX_TIME]"#;
    
    phone.send_fax("+71-23-196-883", fax_content).ok();
    
    println!("The Paradox:");
    println!("  You can't dial numbers bigger than 10^15");
    println!("  But j-invariant is infinite");
    println!("  Solution: Dial coefficients, fax the rest\n");
    
    println!("✅ Level 5 Complete!");
}
