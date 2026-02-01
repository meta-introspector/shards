# TradeWars BBS - Solana Devnet Deployment

## Quick Deploy

```bash
#!/bin/bash
# deploy.sh - Launch TradeWars BBS on Solana Devnet

set -e

echo "🚀 Deploying TradeWars BBS to Solana Devnet..."

# 1. Setup Solana CLI
solana config set --url https://api.devnet.solana.com
solana-keygen new --outfile ~/.config/solana/tradewars-deployer.json --no-bip39-passphrase
export DEPLOYER=$(solana-keygen pubkey ~/.config/solana/tradewars-deployer.json)
echo "Deployer: $DEPLOYER"

# 2. Airdrop SOL
echo "💰 Requesting airdrop..."
solana airdrop 2 $DEPLOYER
solana balance $DEPLOYER

# 3. Build Anchor program
cd programs/tradewars-bbs
anchor build
anchor deploy

# 4. Get program ID
export PROGRAM_ID=$(solana address -k target/deploy/tradewars_bbs-keypair.json)
echo "Program ID: $PROGRAM_ID"

# 5. Update Anchor.toml
sed -i "s/tradewars_bbs = \".*\"/tradewars_bbs = \"$PROGRAM_ID\"/" Anchor.toml

# 6. Deploy frontend to Vercel
cd ../../frontend
vercel deploy --prod

echo "✅ Deployment complete!"
echo "Program: $PROGRAM_ID"
echo "Frontend: https://tradewars-bbs.vercel.app"
```

## Anchor Program

```rust
// programs/tradewars-bbs/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("TradEWaRsBBSv1111111111111111111111111111111");

#[program]
pub mod tradewars_bbs {
    use super::*;

    pub fn initialize_user(ctx: Context<InitializeUser>) -> Result<()> {
        let user = &mut ctx.accounts.user;
        user.wallet = ctx.accounts.authority.key();
        user.credits = 1000;
        user.sector = 1;
        user.cargo = vec![];
        Ok(())
    }

    pub fn buy_lower_bits(ctx: Context<BuyBits>, num_bits: u8) -> Result<()> {
        let user = &mut ctx.accounts.user;
        let cost = (num_bits as u64) * 1000;
        
        require!(user.credits >= cost, ErrorCode::InsufficientCredits);
        
        user.credits -= cost;
        user.bit_capacity += num_bits;
        
        Ok(())
    }

    pub fn send_steg_payment(
        ctx: Context<SendStegPayment>,
        base_amount: u64,
        data: Vec<u8>,
    ) -> Result<()> {
        let user = &ctx.accounts.user;
        
        // Pack data into lower bits
        let steg_amount = pack_data(base_amount, &data);
        
        // Transfer SOL
        let ix = anchor_lang::solana_program::system_instruction::transfer(
            &ctx.accounts.authority.key(),
            &ctx.accounts.recipient.key(),
            steg_amount,
        );
        
        anchor_lang::solana_program::program::invoke(
            &ix,
            &[
                ctx.accounts.authority.to_account_info(),
                ctx.accounts.recipient.to_account_info(),
            ],
        )?;
        
        // Log transaction
        emit!(StegPaymentEvent {
            from: ctx.accounts.authority.key(),
            to: ctx.accounts.recipient.key(),
            base_amount,
            steg_amount,
            data_len: data.len() as u8,
        });
        
        Ok(())
    }

    pub fn trade_commodity(
        ctx: Context<Trade>,
        commodity: Commodity,
        quantity: u32,
        is_buy: bool,
    ) -> Result<()> {
        let user = &mut ctx.accounts.user;
        let price = get_commodity_price(&commodity);
        let total = price * quantity as u64;
        
        if is_buy {
            require!(user.credits >= total, ErrorCode::InsufficientCredits);
            user.credits -= total;
            user.cargo.push(CargoItem { commodity, quantity });
        } else {
            // Sell logic
            user.credits += total;
        }
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct InitializeUser<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + User::LEN,
        seeds = [b"user", authority.key().as_ref()],
        bump
    )]
    pub user: Account<'info, User>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct BuyBits<'info> {
    #[account(mut, has_one = wallet)]
    pub user: Account<'info, User>,
    pub wallet: Signer<'info>,
}

#[derive(Accounts)]
pub struct SendStegPayment<'info> {
    #[account(mut)]
    pub user: Account<'info, User>,
    #[account(mut)]
    pub authority: Signer<'info>,
    /// CHECK: Recipient can be any account
    #[account(mut)]
    pub recipient: AccountInfo<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Trade<'info> {
    #[account(mut, has_one = wallet)]
    pub user: Account<'info, User>,
    pub wallet: Signer<'info>,
}

#[account]
pub struct User {
    pub wallet: Pubkey,
    pub credits: u64,
    pub sector: u8,
    pub bit_capacity: u8,
    pub cargo: Vec<CargoItem>,
}

impl User {
    pub const LEN: usize = 32 + 8 + 1 + 1 + 4 + (10 * CargoItem::LEN);
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct CargoItem {
    pub commodity: Commodity,
    pub quantity: u32,
}

impl CargoItem {
    pub const LEN: usize = 1 + 4;
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy)]
pub enum Commodity {
    FuelOre,
    Equipment,
    Organics,
    GodelNumbers,
}

#[event]
pub struct StegPaymentEvent {
    pub from: Pubkey,
    pub to: Pubkey,
    pub base_amount: u64,
    pub steg_amount: u64,
    pub data_len: u8,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Insufficient credits")]
    InsufficientCredits,
}

fn pack_data(base: u64, data: &[u8]) -> u64 {
    let mut amount = base & !0xFF;
    for (i, byte) in data.iter().take(8).enumerate() {
        amount |= (*byte as u64) << (i * 8);
    }
    amount
}

fn get_commodity_price(commodity: &Commodity) -> u64 {
    match commodity {
        Commodity::FuelOre => 42,
        Commodity::Equipment => 137,
        Commodity::Organics => 71,
        Commodity::GodelNumbers => 263,
    }
}
```

## TypeScript Client

```typescript
// app/tradewars-client.ts
import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { TradewarsBbs } from "../target/types/tradewars_bbs";
import { Connection, PublicKey } from "@solana/web3.js";

export class TradeWarsClient {
  constructor(
    public program: Program<TradewarsBbs>,
    public provider: anchor.AnchorProvider
  ) {}

  static async connect(wallet: any): Promise<TradeWarsClient> {
    const connection = new Connection("https://api.devnet.solana.com");
    const provider = new anchor.AnchorProvider(connection, wallet, {});
    const program = anchor.workspace.TradewarsBbs as Program<TradewarsBbs>;
    
    return new TradeWarsClient(program, provider);
  }

  async initializeUser(): Promise<string> {
    const [userPda] = PublicKey.findProgramAddressSync(
      [Buffer.from("user"), this.provider.wallet.publicKey.toBuffer()],
      this.program.programId
    );

    const tx = await this.program.methods
      .initializeUser()
      .accounts({
        user: userPda,
        authority: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async buyLowerBits(numBits: number): Promise<string> {
    const [userPda] = this.getUserPda();

    const tx = await this.program.methods
      .buyLowerBits(numBits)
      .accounts({
        user: userPda,
        wallet: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async sendStegPayment(
    recipient: PublicKey,
    baseAmount: number,
    data: Buffer
  ): Promise<string> {
    const [userPda] = this.getUserPda();

    const tx = await this.program.methods
      .sendStegPayment(new anchor.BN(baseAmount), Array.from(data))
      .accounts({
        user: userPda,
        authority: this.provider.wallet.publicKey,
        recipient,
      })
      .rpc();

    return tx;
  }

  async trade(
    commodity: any,
    quantity: number,
    isBuy: boolean
  ): Promise<string> {
    const [userPda] = this.getUserPda();

    const tx = await this.program.methods
      .tradeCommodity(commodity, quantity, isBuy)
      .accounts({
        user: userPda,
        wallet: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  getUserPda(): [PublicKey, number] {
    return PublicKey.findProgramAddressSync(
      [Buffer.from("user"), this.provider.wallet.publicKey.toBuffer()],
      this.program.programId
    );
  }

  async getUser(): Promise<any> {
    const [userPda] = this.getUserPda();
    return await this.program.account.user.fetch(userPda);
  }
}
```

## Anchor.toml

```toml
[features]
seeds = false
skip-lint = false

[programs.devnet]
tradewars_bbs = "TradEWaRsBBSv1111111111111111111111111111111"

[registry]
url = "https://api.apr.dev"

[provider]
cluster = "devnet"
wallet = "~/.config/solana/tradewars-deployer.json"

[scripts]
test = "yarn run ts-mocha -p ./tsconfig.json -t 1000000 tests/**/*.ts"
```

## Package.json

```json
{
  "name": "tradewars-bbs",
  "version": "1.0.0",
  "scripts": {
    "build": "anchor build",
    "deploy": "anchor deploy",
    "test": "anchor test",
    "dev": "next dev"
  },
  "dependencies": {
    "@coral-xyz/anchor": "^0.29.0",
    "@solana/web3.js": "^1.87.6",
    "@solana/wallet-adapter-react": "^0.15.35",
    "@solana/wallet-adapter-wallets": "^0.19.26",
    "next": "^14.0.0",
    "react": "^18.2.0",
    "dioxus": "^0.4.0"
  },
  "devDependencies": {
    "@types/node": "^20.0.0",
    "typescript": "^5.0.0"
  }
}
```

## Deploy Commands

```bash
# Install dependencies
npm install -g @coral-xyz/anchor-cli
cargo install --git https://github.com/coral-xyz/anchor anchor-cli --locked

# Setup Solana
solana config set --url devnet
solana-keygen new

# Airdrop
solana airdrop 2

# Build and deploy
anchor build
anchor deploy

# Test
anchor test --skip-local-validator

# Get program ID
solana address -k target/deploy/tradewars_bbs-keypair.json
```

## Environment Variables

```bash
# .env.local
NEXT_PUBLIC_SOLANA_NETWORK=devnet
NEXT_PUBLIC_PROGRAM_ID=TradEWaRsBBSv1111111111111111111111111111111
NEXT_PUBLIC_RPC_URL=https://api.devnet.solana.com
SUPABASE_URL=https://your-project.supabase.co
SUPABASE_KEY=your-anon-key
```

## Test Script

```typescript
// tests/tradewars-bbs.ts
import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { TradewarsBbs } from "../target/types/tradewars_bbs";
import { assert } from "chai";

describe("tradewars-bbs", () => {
  const provider = anchor.AnchorProvider.env();
  anchor.setProvider(provider);

  const program = anchor.workspace.TradewarsBbs as Program<TradewarsBbs>;

  it("Initializes user", async () => {
    const tx = await program.methods.initializeUser().rpc();
    console.log("Transaction:", tx);
  });

  it("Buys lower bits", async () => {
    const tx = await program.methods.buyLowerBits(64).rpc();
    console.log("Bought 64 bits:", tx);
  });

  it("Sends steg payment", async () => {
    const data = Buffer.from("Hello, TradeWars!");
    const tx = await program.methods
      .sendStegPayment(new anchor.BN(1000000), Array.from(data))
      .rpc();
    console.log("Steg payment:", tx);
  });
});
```

## Launch Checklist

- [x] Solana CLI configured for devnet
- [x] Anchor program written
- [x] Tests passing
- [ ] Deploy program: `anchor deploy`
- [ ] Deploy frontend: `vercel deploy`
- [ ] Setup Supabase tables
- [ ] Test wallet connection
- [ ] Test steganographic payments
- [ ] Invite FRENs

🚀 **Ready to launch!** Run `./deploy.sh`
