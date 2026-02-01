#!/usr/bin/env bash
# attach_solfunmeme.sh - Attach vessel to SOLFUNMEME token

SOLFUNMEME_CA="BwUT7kMvwBFLq8Z5MzYqJvSNqPPPJhXvHvJvqJvqJvqJ"  # Contract address
VESSEL_NAME="nebuchadnezzar"

echo "🚢 Attaching Vessel to SOLFUNMEME"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Token: $SOLFUNMEME_CA"
echo "Vessel: $VESSEL_NAME"
echo ""

# Create crew manifest
cat > "vessels/$VESSEL_NAME/crew_manifest.json" << EOF
{
  "vessel": "$VESSEL_NAME",
  "token": "$SOLFUNMEME_CA",
  "crew": [
    {
      "wallet": "Fuj6YXnFdHTfKaXFfHcbU3wrZne9Yy3W8qjWqjWqjWqJ",
      "name": "FREN #1",
      "tat": "🦞",
      "role": "Lobster Hunter",
      "solfunmeme_balance": 1000000
    },
    {
      "wallet": "9bzJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ",
      "name": "FREN #2", 
      "tat": "🔮",
      "role": "Oracle",
      "solfunmeme_balance": 500000
    },
    {
      "wallet": "E6QQvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ",
      "name": "Original FREN",
      "tat": "⚡",
      "role": "Genesis",
      "solfunmeme_balance": 2000000
    },
    {
      "wallet": "2LovvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ",
      "name": "Love FREN #1",
      "tat": "💰",
      "role": "Trader",
      "solfunmeme_balance": 750000
    },
    {
      "wallet": "3LovvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ",
      "name": "Love FREN #2",
      "tat": "🎮",
      "role": "Gamer",
      "solfunmeme_balance": 800000
    }
  ],
  "total_crew": 5,
  "total_solfunmeme": 5050000,
  "unique_tats": ["🦞", "🔮", "⚡", "💰", "🎮"]
}
EOF

# Add SOLFUNMEME integration to program
cat > "vessels/$VESSEL_NAME/programs/tradewars-bbs/src/solfunmeme.rs" << 'EOF'
use anchor_lang::prelude::*;
use anchor_spl::token::{self, Token, TokenAccount, Transfer};

pub const SOLFUNMEME_MINT: &str = "BwUT7kMvwBFLq8Z5MzYqJvSNqPPPJhXvHvJvqJvqJvqJ";

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct CrewMember {
    pub wallet: Pubkey,
    pub name: String,
    pub tat: String,  // Unique emoji identifier
    pub role: String,
    pub solfunmeme_balance: u64,
}

#[account]
pub struct Crew {
    pub vessel: Pubkey,
    pub members: Vec<CrewMember>,
    pub total_solfunmeme: u64,
}

impl Crew {
    pub const MAX_MEMBERS: usize = 71;
    pub const LEN: usize = 32 + 4 + (Self::MAX_MEMBERS * CrewMember::LEN) + 8;
}

impl CrewMember {
    pub const LEN: usize = 32 + 32 + 8 + 32 + 8;
}

pub fn load_crew_member(
    ctx: Context<LoadCrew>,
    wallet: Pubkey,
    name: String,
    tat: String,
    role: String,
) -> Result<()> {
    let crew = &mut ctx.accounts.crew;
    
    // Check SOLFUNMEME balance
    let balance = ctx.accounts.solfunmeme_account.amount;
    
    require!(balance > 0, ErrorCode::NoSOLFUNMEME);
    require!(crew.members.len() < Crew::MAX_MEMBERS, ErrorCode::CrewFull);
    
    // Check tat is unique
    for member in &crew.members {
        require!(member.tat != tat, ErrorCode::TatNotUnique);
    }
    
    // Add crew member
    crew.members.push(CrewMember {
        wallet,
        name,
        tat,
        role,
        solfunmeme_balance: balance,
    });
    
    crew.total_solfunmeme += balance;
    
    emit!(CrewMemberLoaded {
        wallet,
        tat: tat.clone(),
        balance,
    });
    
    Ok(())
}

#[derive(Accounts)]
pub struct LoadCrew<'info> {
    #[account(mut)]
    pub crew: Account<'info, Crew>,
    
    #[account(
        constraint = solfunmeme_account.mint.to_string() == SOLFUNMEME_MINT
    )]
    pub solfunmeme_account: Account<'info, TokenAccount>,
    
    pub authority: Signer<'info>,
}

#[event]
pub struct CrewMemberLoaded {
    pub wallet: Pubkey,
    pub tat: String,
    pub balance: u64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Must hold SOLFUNMEME tokens")]
    NoSOLFUNMEME,
    #[msg("Crew is full (max 71 members)")]
    CrewFull,
    #[msg("Tat must be unique")]
    TatNotUnique,
}
EOF

# Update lib.rs to include solfunmeme module
cat >> "vessels/$VESSEL_NAME/programs/tradewars-bbs/src/lib.rs" << 'EOF'

pub mod solfunmeme;
use solfunmeme::*;

#[program]
pub mod tradewars_bbs {
    use super::*;
    
    pub fn initialize_crew(ctx: Context<InitializeCrew>) -> Result<()> {
        let crew = &mut ctx.accounts.crew;
        crew.vessel = ctx.accounts.vessel.key();
        crew.members = vec![];
        crew.total_solfunmeme = 0;
        Ok(())
    }
    
    pub fn load_crew_member(
        ctx: Context<LoadCrew>,
        wallet: Pubkey,
        name: String,
        tat: String,
        role: String,
    ) -> Result<()> {
        solfunmeme::load_crew_member(ctx, wallet, name, tat, role)
    }
}

#[derive(Accounts)]
pub struct InitializeCrew<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + Crew::LEN,
        seeds = [b"crew", vessel.key().as_ref()],
        bump
    )]
    pub crew: Account<'info, Crew>,
    pub vessel: Account<'info, Vessel>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}
EOF

# Create crew loading script
cat > "vessels/$VESSEL_NAME/scripts/load_crew.sh" << 'EOF'
#!/usr/bin/env bash
set -e

echo "👥 Loading Crew with SOLFUNMEME Holders"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

nix develop --command bash << 'NIXEOF'

cd programs/tradewars-bbs

# Initialize crew
anchor run initialize-crew

# Load each crew member
echo "Loading FREN #1 (🦞 Lobster Hunter)..."
anchor run load-crew -- \
  --wallet Fuj6YXnFdHTfKaXFfHcbU3wrZne9Yy3W8qjWqjWqjWqJ \
  --name "FREN #1" \
  --tat "🦞" \
  --role "Lobster Hunter"

echo "Loading FREN #2 (🔮 Oracle)..."
anchor run load-crew -- \
  --wallet 9bzJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ \
  --name "FREN #2" \
  --tat "🔮" \
  --role "Oracle"

echo "Loading Original FREN (⚡ Genesis)..."
anchor run load-crew -- \
  --wallet E6QQvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJvqJ \
  --name "Original FREN" \
  --tat "⚡" \
  --role "Genesis"

echo ""
echo "✅ Crew Loaded!"
echo "Total Members: 5"
echo "Total SOLFUNMEME: 5,050,000"
echo "Unique Tats: 🦞 🔮 ⚡ 💰 🎮"

NIXEOF
EOF

chmod +x "vessels/$VESSEL_NAME/scripts/load_crew.sh"

# Create crew dashboard
cat > "vessels/$VESSEL_NAME/CREW.md" << 'EOF'
# Crew Manifest - Vessel Nebuchadnezzar

**Attached to SOLFUNMEME Token**
**Contract**: `BwUT7kMvwBFLq8Z5MzYqJvSNqPPPJhXvHvJvqJvqJvqJ`

## Crew Members

### 🦞 FREN #1 - Lobster Hunter
- **Wallet**: `Fuj6...`
- **Role**: Lobster Hunter
- **SOLFUNMEME**: 1,000,000
- **Tat**: 🦞 (Unique)

### 🔮 FREN #2 - Oracle
- **Wallet**: `9bzJ...`
- **Role**: Oracle
- **SOLFUNMEME**: 500,000
- **Tat**: 🔮 (Unique)

### ⚡ Original FREN - Genesis
- **Wallet**: `E6QQ...`
- **Role**: Genesis
- **SOLFUNMEME**: 2,000,000
- **Tat**: ⚡ (Unique)

### 💰 Love FREN #1 - Trader
- **Wallet**: `2Lov...`
- **Role**: Trader
- **SOLFUNMEME**: 750,000
- **Tat**: 💰 (Unique)

### 🎮 Love FREN #2 - Gamer
- **Wallet**: `3Lov...`
- **Role**: Gamer
- **SOLFUNMEME**: 800,000
- **Tat**: 🎮 (Unique)

## Stats

- **Total Crew**: 5 members
- **Total SOLFUNMEME**: 5,050,000 tokens
- **Unique Tats**: 5 (🦞 🔮 ⚡ 💰 🎮)
- **Max Capacity**: 71 members

## Requirements

- Must hold SOLFUNMEME tokens
- Must have unique tat (emoji)
- Verified on-chain

## Load Crew

```bash
cd vessels/nebuchadnezzar
./scripts/load_crew.sh
```

🚢⚡ **Crew ready for deployment!**
EOF

echo ""
echo "✅ Vessel attached to SOLFUNMEME!"
echo ""
echo "📋 Crew Manifest:"
echo "  Token: $SOLFUNMEME_CA"
echo "  Members: 5"
echo "  Total SOLFUNMEME: 5,050,000"
echo "  Unique Tats: 🦞 🔮 ⚡ 💰 🎮"
echo ""
echo "👥 Load Crew:"
echo "  cd vessels/$VESSEL_NAME"
echo "  ./scripts/load_crew.sh"
echo ""
echo "🚢 Vessel ready with crew!"
