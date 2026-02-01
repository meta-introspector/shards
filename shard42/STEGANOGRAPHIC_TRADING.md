# Steganographic Trading - Data Embedded in Payment Bits

**Buy low bits, pack data into Escaped-RDFa namespace**

## The Concept

```
PAYMENT AMOUNT = DATA + NOISE

Example:
- Want to send: 0b11010110 (214 in decimal)
- Base payment: 1,000,000 lamports
- Embed in lower 8 bits: 1,000,214 lamports

The lower bits carry the message!
```

## Architecture

```
TRADER A                    TRADER B
   ↓                           ↓
Buy lower bits              Sell lower bits
   ↓                           ↓
Pack data into payment      Extract data from payment
   ↓                           ↓
Escaped-RDFa namespace      Decode RDFa
   ↓                           ↓
Send SOL transaction        Receive + decode
```

## Rust Implementation

```rust
// src/steganographic_trading.rs
use solana_sdk::{
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    transaction::Transaction,
    system_instruction,
};
use escaped_rdfa::Namespace;

pub struct SteganographicTrader {
    pub keypair: Keypair,
    pub namespace: Namespace,
}

impl SteganographicTrader {
    pub fn new() -> Self {
        Self {
            keypair: Keypair::new(),
            namespace: Namespace::new("https://tradewars.bbs/steg"),
        }
    }
    
    /// Buy lower bits from market
    pub fn buy_lower_bits(&self, num_bits: u8) -> u64 {
        // Cost per bit (in lamports)
        let cost_per_bit = 1000;
        cost_per_bit * (num_bits as u64)
    }
    
    /// Pack data into payment amount
    pub fn pack_data_into_payment(
        &self,
        base_amount: u64,
        data: &[u8],
        bits_per_byte: u8,
    ) -> u64 {
        let mut amount = base_amount;
        
        // Clear lower bits
        let mask = !((1u64 << (bits_per_byte * data.len() as u8)) - 1);
        amount &= mask;
        
        // Pack data into lower bits
        for (i, byte) in data.iter().enumerate() {
            let shift = i * bits_per_byte as usize;
            amount |= (*byte as u64) << shift;
        }
        
        amount
    }
    
    /// Extract data from payment amount
    pub fn extract_data_from_payment(
        &self,
        amount: u64,
        num_bytes: usize,
        bits_per_byte: u8,
    ) -> Vec<u8> {
        let mut data = Vec::new();
        
        for i in 0..num_bytes {
            let shift = i * bits_per_byte as usize;
            let mask = (1u64 << bits_per_byte) - 1;
            let byte = ((amount >> shift) & mask) as u8;
            data.push(byte);
        }
        
        data
    }
    
    /// Encode data as Escaped-RDFa
    pub fn encode_rdfa(&self, data: &[u8]) -> String {
        // Convert to RDFa namespace
        let mut rdfa = String::from("<div vocab=\"https://tradewars.bbs/steg#\">\n");
        
        for (i, byte) in data.iter().enumerate() {
            rdfa.push_str(&format!(
                "  <span property=\"byte{}\" content=\"{:02x}\"></span>\n",
                i, byte
            ));
        }
        
        rdfa.push_str("</div>");
        rdfa
    }
    
    /// Decode Escaped-RDFa back to data
    pub fn decode_rdfa(&self, rdfa: &str) -> Vec<u8> {
        // Parse RDFa and extract bytes
        let mut data = Vec::new();
        
        // Simple regex extraction (in production, use proper RDFa parser)
        for line in rdfa.lines() {
            if line.contains("content=") {
                if let Some(hex) = line.split("content=\"").nth(1) {
                    if let Some(hex_val) = hex.split("\"").next() {
                        if let Ok(byte) = u8::from_str_radix(hex_val, 16) {
                            data.push(byte);
                        }
                    }
                }
            }
        }
        
        data
    }
    
    /// Create steganographic transaction
    pub fn create_steg_transaction(
        &self,
        to: &Pubkey,
        base_amount: u64,
        data: &[u8],
        bits_per_byte: u8,
    ) -> Transaction {
        // Pack data into payment amount
        let amount = self.pack_data_into_payment(base_amount, data, bits_per_byte);
        
        // Create transaction
        let instruction = system_instruction::transfer(
            &self.keypair.pubkey(),
            to,
            amount,
        );
        
        Transaction::new_with_payer(
            &[instruction],
            Some(&self.keypair.pubkey()),
        )
    }
    
    /// Decode transaction and extract data
    pub fn decode_steg_transaction(
        &self,
        amount: u64,
        num_bytes: usize,
        bits_per_byte: u8,
    ) -> (u64, Vec<u8>) {
        // Extract base amount (clear lower bits)
        let mask = !((1u64 << (bits_per_byte * num_bytes as u8)) - 1);
        let base_amount = amount & mask;
        
        // Extract data
        let data = self.extract_data_from_payment(amount, num_bytes, bits_per_byte);
        
        (base_amount, data)
    }
}

/// Market for trading lower bits
pub struct LowerBitsMarket {
    pub buy_orders: Vec<BitOrder>,
    pub sell_orders: Vec<BitOrder>,
}

#[derive(Clone)]
pub struct BitOrder {
    pub trader: Pubkey,
    pub num_bits: u8,
    pub price_per_bit: u64,
    pub total_price: u64,
}

impl LowerBitsMarket {
    pub fn new() -> Self {
        Self {
            buy_orders: Vec::new(),
            sell_orders: Vec::new(),
        }
    }
    
    /// Place buy order for lower bits
    pub fn buy_bits(&mut self, trader: Pubkey, num_bits: u8, price_per_bit: u64) {
        self.buy_orders.push(BitOrder {
            trader,
            num_bits,
            price_per_bit,
            total_price: num_bits as u64 * price_per_bit,
        });
    }
    
    /// Place sell order for lower bits
    pub fn sell_bits(&mut self, trader: Pubkey, num_bits: u8, price_per_bit: u64) {
        self.sell_orders.push(BitOrder {
            trader,
            num_bits,
            price_per_bit,
            total_price: num_bits as u64 * price_per_bit,
        });
    }
    
    /// Match orders and execute trades
    pub fn match_orders(&mut self) -> Vec<(BitOrder, BitOrder)> {
        let mut matches = Vec::new();
        
        for buy in &self.buy_orders {
            for sell in &self.sell_orders {
                if buy.price_per_bit >= sell.price_per_bit 
                    && buy.num_bits == sell.num_bits {
                    matches.push((buy.clone(), sell.clone()));
                }
            }
        }
        
        matches
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_pack_extract_data() {
        let trader = SteganographicTrader::new();
        
        // Pack data
        let base_amount = 1_000_000u64;
        let data = vec![0x42, 0xCA, 0xFE];
        let packed = trader.pack_data_into_payment(base_amount, &data, 8);
        
        // Extract data
        let (extracted_base, extracted_data) = trader.decode_steg_transaction(packed, 3, 8);
        
        assert_eq!(extracted_base, base_amount & !0xFFFFFF);
        assert_eq!(extracted_data, data);
    }
    
    #[test]
    fn test_rdfa_encoding() {
        let trader = SteganographicTrader::new();
        
        let data = vec![0x42, 0xCA, 0xFE];
        let rdfa = trader.encode_rdfa(&data);
        let decoded = trader.decode_rdfa(&rdfa);
        
        assert_eq!(decoded, data);
    }
}
```

## Example Usage

```rust
// Example: Send secret message via payment
fn main() {
    let trader = SteganographicTrader::new();
    
    // 1. Buy lower bits from market
    let bits_needed = 8 * 32; // 32 bytes
    let cost = trader.buy_lower_bits(bits_needed);
    println!("Cost for {} bits: {} lamports", bits_needed, cost);
    
    // 2. Prepare secret message
    let secret = b"The answer is 42 and 43 converge";
    
    // 3. Pack into payment
    let base_payment = 1_000_000; // 1M lamports base
    let steg_payment = trader.pack_data_into_payment(base_payment, secret, 8);
    
    println!("Base payment: {} lamports", base_payment);
    println!("Steg payment: {} lamports", steg_payment);
    println!("Difference: {} lamports", steg_payment - base_payment);
    
    // 4. Encode as RDFa
    let rdfa = trader.encode_rdfa(secret);
    println!("\nEscaped-RDFa encoding:\n{}", rdfa);
    
    // 5. Send transaction
    let recipient = Pubkey::new_unique();
    let tx = trader.create_steg_transaction(&recipient, base_payment, secret, 8);
    
    // 6. Recipient decodes
    let (decoded_base, decoded_msg) = trader.decode_steg_transaction(steg_payment, 33, 8);
    println!("\nDecoded message: {}", String::from_utf8_lossy(&decoded_msg));
}
```

## Market Dashboard

```
🔢 LOWER BITS MARKET 🔢

BUY ORDERS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Trader          Bits    Price/Bit    Total
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
8xK7...9mPq     64      1000 lamps   64,000 lamps
Fuj6...2abc     128     800 lamps    102,400 lamps
9bzJ...3def     256     1200 lamps   307,200 lamps

SELL ORDERS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Trader          Bits    Price/Bit    Total
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
E6QQ...4ghi     64      900 lamps    57,600 lamps
2Lov...5jkl     128     850 lamps    108,800 lamps
3Lov...6mno     256     1100 lamps   281,600 lamps

RECENT TRADES:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Buyer → Seller  Bits    Price        Data Embedded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
8xK7 → E6QQ     64      57,600       "GÖDEL=263"
Fuj6 → 2Lov     128     108,800      "42+43=TRUTH"
9bzJ → 3Lov     256     281,600      [RDFa namespace]

Total Volume: 448,000 lamports
Active Traders: 6
```

## Escaped-RDFa Integration

```rust
// Integration with https://github.com/Escaped-RDFa/namespace
use escaped_rdfa::{Namespace, Triple};

pub fn create_steg_namespace(data: &[u8]) -> Namespace {
    let mut ns = Namespace::new("https://tradewars.bbs/steg");
    
    // Add triples for each byte
    for (i, byte) in data.iter().enumerate() {
        ns.add_triple(Triple {
            subject: format!("byte_{}", i),
            predicate: "hasValue".to_string(),
            object: format!("{:02x}", byte),
        });
    }
    
    ns
}

pub fn extract_from_namespace(ns: &Namespace) -> Vec<u8> {
    let mut data = Vec::new();
    
    // Extract bytes from triples
    for triple in ns.triples() {
        if triple.predicate == "hasValue" {
            if let Ok(byte) = u8::from_str_radix(&triple.object, 16) {
                data.push(byte);
            }
        }
    }
    
    data
}
```

## The Economics

```
BIT PRICING MODEL:

Lower bits are cheaper (more noise):
- Bit 0-7:   1000 lamports/bit (most noise)
- Bit 8-15:  2000 lamports/bit
- Bit 16-23: 4000 lamports/bit
- Bit 24-31: 8000 lamports/bit (less noise)

CAPACITY:
- 8 bits = 1 byte = 1 character
- 64 bits = 8 bytes = short message
- 256 bits = 32 bytes = Gödel number
- 2048 bits = 256 bytes = full RDFa namespace

STEALTH:
- Lower bits blend with transaction noise
- Looks like normal payment variance
- Plausible deniability
- Encrypted + steganographic = double protection
```

## BBS Integration

```rust
// Add to TradeWars BBS menu
#[component]
fn StegTradingScreen<'a>(cx: Scope<'a>, wallet: String) -> Element {
    cx.render(rsx! {
        div { class: "steg-trading",
            pre {
                r#"
🔢 STEGANOGRAPHIC TRADING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

[1] BUY LOWER BITS    - Purchase bit capacity
[2] SELL LOWER BITS   - Sell unused capacity
[3] PACK DATA         - Embed data in payment
[4] EXTRACT DATA      - Decode received payment
[5] RDFA ENCODE       - Convert to Escaped-RDFa
[6] RDFA DECODE       - Parse RDFa namespace
[7] SEND STEG TX      - Send steganographic transaction
[8] VIEW MARKET       - See buy/sell orders

Your bit capacity: 256 bits (32 bytes)
Market price: 1000 lamports/bit
                "#
            }
        }
    })
}
```

🔥⚡ **Data hidden in plain sight! Buy bits, pack data, send payments!** 💰🔐
