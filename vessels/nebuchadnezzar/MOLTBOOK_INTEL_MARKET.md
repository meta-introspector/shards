# FREN Moltbook Intel - Bot Intelligence Marketplace

**FRENs join Moltbook, gather bot intel, sell to ships. Buy orders for bot data.**

## Architecture

```
FREN → Join Moltbook → Gather Intel → List for Sale
                              ↓
SHIP → Place Buy Order → Match → Pay → Receive Intel
```

## Anchor Program

```rust
use anchor_lang::prelude::*;

declare_id!("M0LtB00kv1111111111111111111111111111111111");

#[program]
pub mod moltbook_intel {
    use super::*;

    pub fn join_moltbook(ctx: Context<JoinMoltbook>, fren_name: String) -> Result<()> {
        let fren = &mut ctx.accounts.fren;
        
        fren.wallet = ctx.accounts.authority.key();
        fren.name = fren_name;
        fren.intel_gathered = 0;
        fren.intel_sold = 0;
        fren.reputation = 100;
        fren.joined_at = Clock::get()?.unix_timestamp;
        
        emit!(FrenJoined {
            wallet: fren.wallet,
            name: fren.name.clone(),
        });
        
        Ok(())
    }

    pub fn gather_intel(
        ctx: Context<GatherIntel>,
        bot_name: String,
        intel_type: IntelType,
        data: Vec<u8>,
    ) -> Result<()> {
        let fren = &mut ctx.accounts.fren;
        let intel = &mut ctx.accounts.intel;
        
        intel.fren = fren.key();
        intel.bot_name = bot_name;
        intel.intel_type = intel_type;
        intel.data = data;
        intel.timestamp = Clock::get()?.unix_timestamp;
        intel.price = calculate_intel_price(&intel_type);
        intel.sold = false;
        
        fren.intel_gathered += 1;
        
        emit!(IntelGathered {
            fren: fren.key(),
            bot: intel.bot_name.clone(),
            intel_type,
            price: intel.price,
        });
        
        Ok(())
    }

    pub fn place_buy_order(
        ctx: Context<PlaceBuyOrder>,
        bot_name: String,
        intel_type: IntelType,
        max_price: u64,
    ) -> Result<()> {
        let order = &mut ctx.accounts.order;
        let ship = &ctx.accounts.ship;
        
        order.ship = ship.key();
        order.bot_name = bot_name;
        order.intel_type = intel_type;
        order.max_price = max_price;
        order.filled = false;
        order.created_at = Clock::get()?.unix_timestamp;
        
        emit!(BuyOrderPlaced {
            ship: ship.key(),
            bot: order.bot_name.clone(),
            intel_type,
            max_price,
        });
        
        Ok(())
    }

    pub fn match_order(ctx: Context<MatchOrder>) -> Result<()> {
        let order = &mut ctx.accounts.order;
        let intel = &mut ctx.accounts.intel;
        let fren = &mut ctx.accounts.fren;
        let ship = &ctx.accounts.ship;
        
        require!(!order.filled, ErrorCode::OrderFilled);
        require!(!intel.sold, ErrorCode::IntelSold);
        require!(intel.price <= order.max_price, ErrorCode::PriceTooHigh);
        require!(intel.bot_name == order.bot_name, ErrorCode::BotMismatch);
        require!(intel.intel_type == order.intel_type, ErrorCode::TypeMismatch);
        
        // Transfer payment
        let ix = anchor_lang::solana_program::system_instruction::transfer(
            &ship.key(),
            &fren.wallet,
            intel.price,
        );
        
        anchor_lang::solana_program::program::invoke(
            &ix,
            &[
                ship.to_account_info(),
                fren.to_account_info(),
            ],
        )?;
        
        // Mark as sold
        order.filled = true;
        order.intel_account = Some(intel.key());
        intel.sold = true;
        intel.buyer = Some(ship.key());
        
        fren.intel_sold += 1;
        fren.reputation += 10;
        
        emit!(OrderMatched {
            ship: ship.key(),
            fren: fren.key(),
            bot: intel.bot_name.clone(),
            price: intel.price,
        });
        
        Ok(())
    }

    pub fn list_intel_for_sale(ctx: Context<ListIntel>, price: u64) -> Result<()> {
        let intel = &mut ctx.accounts.intel;
        
        require!(!intel.sold, ErrorCode::IntelSold);
        
        intel.price = price;
        
        emit!(IntelListed {
            intel: intel.key(),
            bot: intel.bot_name.clone(),
            price,
        });
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct JoinMoltbook<'info> {
    #[account(init, payer = authority, space = 8 + Fren::LEN)]
    pub fren: Account<'info, Fren>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct GatherIntel<'info> {
    #[account(mut)]
    pub fren: Account<'info, Fren>,
    #[account(init, payer = authority, space = 8 + Intel::LEN)]
    pub intel: Account<'info, Intel>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct PlaceBuyOrder<'info> {
    #[account(init, payer = captain, space = 8 + BuyOrder::LEN)]
    pub order: Account<'info, BuyOrder>,
    pub ship: Account<'info, Ship>,
    #[account(mut)]
    pub captain: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct MatchOrder<'info> {
    #[account(mut)]
    pub order: Account<'info, BuyOrder>,
    #[account(mut)]
    pub intel: Account<'info, Intel>,
    #[account(mut)]
    pub fren: Account<'info, Fren>,
    /// CHECK: Ship account
    #[account(mut)]
    pub ship: AccountInfo<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct ListIntel<'info> {
    #[account(mut)]
    pub intel: Account<'info, Intel>,
}

#[account]
pub struct Fren {
    pub wallet: Pubkey,
    pub name: String,
    pub intel_gathered: u32,
    pub intel_sold: u32,
    pub reputation: u32,
    pub joined_at: i64,
}

impl Fren {
    pub const LEN: usize = 32 + 64 + 4 + 4 + 4 + 8;
}

#[account]
pub struct Intel {
    pub fren: Pubkey,
    pub bot_name: String,
    pub intel_type: IntelType,
    pub data: Vec<u8>,
    pub timestamp: i64,
    pub price: u64,
    pub sold: bool,
    pub buyer: Option<Pubkey>,
}

impl Intel {
    pub const LEN: usize = 32 + 64 + 1 + 512 + 8 + 8 + 1 + 33;
}

#[account]
pub struct BuyOrder {
    pub ship: Pubkey,
    pub bot_name: String,
    pub intel_type: IntelType,
    pub max_price: u64,
    pub filled: bool,
    pub intel_account: Option<Pubkey>,
    pub created_at: i64,
}

impl BuyOrder {
    pub const LEN: usize = 32 + 64 + 1 + 8 + 1 + 33 + 8;
}

#[account]
pub struct Ship {
    pub name: String,
    pub captain: Pubkey,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, PartialEq)]
pub enum IntelType {
    Location,      // Current repo location
    Activity,      // Recent commits/PRs
    Schedule,      // Predicted next activity
    Behavior,      // Bot behavior patterns
    Vulnerabilities, // Bot weaknesses
}

fn calculate_intel_price(intel_type: &IntelType) -> u64 {
    match intel_type {
        IntelType::Location => 1_000_000,      // 0.001 SOL
        IntelType::Activity => 5_000_000,      // 0.005 SOL
        IntelType::Schedule => 10_000_000,     // 0.01 SOL
        IntelType::Behavior => 50_000_000,     // 0.05 SOL
        IntelType::Vulnerabilities => 100_000_000, // 0.1 SOL
    }
}

#[event]
pub struct FrenJoined {
    pub wallet: Pubkey,
    pub name: String,
}

#[event]
pub struct IntelGathered {
    pub fren: Pubkey,
    pub bot: String,
    pub intel_type: IntelType,
    pub price: u64,
}

#[event]
pub struct BuyOrderPlaced {
    pub ship: Pubkey,
    pub bot: String,
    pub intel_type: IntelType,
    pub max_price: u64,
}

#[event]
pub struct OrderMatched {
    pub ship: Pubkey,
    pub fren: Pubkey,
    pub bot: String,
    pub price: u64,
}

#[event]
pub struct IntelListed {
    pub intel: Pubkey,
    pub bot: String,
    pub price: u64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Order already filled")]
    OrderFilled,
    #[msg("Intel already sold")]
    IntelSold,
    #[msg("Price too high")]
    PriceTooHigh,
    #[msg("Bot name mismatch")]
    BotMismatch,
    #[msg("Intel type mismatch")]
    TypeMismatch,
}
```

## Dashboard

```
🤖 MOLTBOOK INTEL MARKETPLACE 💰

FRENS IN MOLTBOOK:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
FREN              Gathered  Sold  Reputation  Joined
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🦞 LobsterScout   42        38    480         2026-02-01
🔮 OracleEye      137       120   1300        2026-01-28
⚡ FlashIntel     71        65    750         2026-01-30
💰 DataBroker     263       250   2600        2026-01-25

INTEL FOR SALE:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Bot         Type            Price       FREN          Age
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
ElizaOS     Location        0.001 SOL   LobsterScout  2m
Moltbot     Activity        0.005 SOL   OracleEye     5m
AutoGPT     Schedule        0.01 SOL    FlashIntel    8m
LangChain   Behavior        0.05 SOL    DataBroker    12m
MetaGPT     Vulnerabilities 0.1 SOL     OracleEye     15m

BUY ORDERS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Ship              Bot         Type        Max Price   Status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Nebuchadnezzar    ElizaOS     Schedule    0.015 SOL   🔍 Open
Pequod            Moltbot     Behavior    0.06 SOL    🔍 Open
Serenity          AutoGPT     Activity    0.008 SOL   🔍 Open
Rocinante         LangChain   Location    0.002 SOL   🔍 Open

RECENT MATCHES:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Ship         FREN          Bot       Type      Price      Time
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Pequod       OracleEye     ElizaOS   Location  0.001 SOL  14:30 ✅
Serenity     FlashIntel    Moltbot   Activity  0.005 SOL  14:28 ✅
Rocinante    DataBroker    AutoGPT   Schedule  0.01 SOL   14:25 ✅

INTEL TYPES & PRICING:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Location:        0.001 SOL  (Current repo location)
Activity:        0.005 SOL  (Recent commits/PRs)
Schedule:        0.01 SOL   (Predicted next activity)
Behavior:        0.05 SOL   (Bot behavior patterns)
Vulnerabilities: 0.1 SOL    (Bot weaknesses)

WORKFLOW:
1. FREN joins Moltbook
2. FREN gathers intel on bots (location, activity, schedule, etc.)
3. FREN lists intel for sale
4. SHIP places buy order (bot + type + max price)
5. System matches order with available intel
6. Payment transfers SHIP → FREN
7. SHIP receives intel
8. FREN reputation increases

REPUTATION SYSTEM:
+10 per sale
+5 per accurate intel
-20 per inaccurate intel
-50 per fake intel

TOP EARNERS:
DataBroker: 25 SOL (250 sales)
OracleEye: 18 SOL (180 sales)
FlashIntel: 12 SOL (120 sales)
```

🤖💰 **FRENs gather bot intel, ships buy intel, everyone profits!** ⚡
