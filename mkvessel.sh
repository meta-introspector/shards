#!/usr/bin/env bash
# mkvessel.sh - Prepare deployment vessel

VESSEL_NAME="${1:-nebuchadnezzar}"

echo "🚢 Preparing Vessel: $VESSEL_NAME"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Create vessel structure
mkdir -p "vessels/$VESSEL_NAME"/{programs,frontend,scripts,config}

cat > "vessels/$VESSEL_NAME/flake.nix" << 'EOF'
{
  description = "Vessel: Nebuchadnezzar - TradeWars BBS Deployment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay, ... }: {
    devShells.x86_64-linux.default = 
      let
        pkgs = import nixpkgs {
          system = "x86_64-linux";
          overlays = [ rust-overlay.overlays.default ];
        };
      in pkgs.mkShell {
        buildInputs = with pkgs; [
          (rust-bin.stable.latest.default.override {
            extensions = [ "rust-src" ];
            targets = [ "wasm32-unknown-unknown" ];
          })
          solana-cli
          nodejs_20
          dioxus-cli
        ];
        
        shellHook = ''
          echo "🚢 Vessel: Nebuchadnezzar Ready"
          echo "Solana: $(solana --version)"
          solana config set --url https://api.devnet.solana.com
        '';
      };
  };
}
EOF

cat > "vessels/$VESSEL_NAME/Cargo.toml" << 'EOF'
[workspace]
members = [
    "programs/tradewars-bbs",
    "frontend",
]

[workspace.package]
version = "1.0.0"
edition = "2021"

[profile.release]
opt-level = "z"
lto = true
codegen-units = 1
EOF

cat > "vessels/$VESSEL_NAME/programs/tradewars-bbs/Cargo.toml" << 'EOF'
[package]
name = "tradewars-bbs"
version = "1.0.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "lib"]

[dependencies]
anchor-lang = "0.29.0"
anchor-spl = "0.29.0"

[dev-dependencies]
solana-program-test = "1.17"
EOF

cat > "vessels/$VESSEL_NAME/programs/tradewars-bbs/src/lib.rs" << 'EOF'
use anchor_lang::prelude::*;

declare_id!("TradEWaRsBBSv1111111111111111111111111111111");

#[program]
pub mod tradewars_bbs {
    use super::*;

    pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
        let vessel = &mut ctx.accounts.vessel;
        vessel.name = "Nebuchadnezzar".to_string();
        vessel.captain = ctx.accounts.authority.key();
        vessel.credits = 1_000_000;
        vessel.sector = 1;
        Ok(())
    }

    pub fn warp(ctx: Context<Warp>, target_sector: u8) -> Result<()> {
        let vessel = &mut ctx.accounts.vessel;
        vessel.sector = target_sector;
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + Vessel::LEN,
        seeds = [b"vessel", authority.key().as_ref()],
        bump
    )]
    pub vessel: Account<'info, Vessel>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Warp<'info> {
    #[account(mut)]
    pub vessel: Account<'info, Vessel>,
    pub authority: Signer<'info>,
}

#[account]
pub struct Vessel {
    pub name: String,
    pub captain: Pubkey,
    pub credits: u64,
    pub sector: u8,
}

impl Vessel {
    pub const LEN: usize = 4 + 32 + 32 + 8 + 1;
}
EOF

cat > "vessels/$VESSEL_NAME/Anchor.toml" << 'EOF'
[features]
seeds = false

[programs.devnet]
tradewars_bbs = "TradEWaRsBBSv1111111111111111111111111111111"

[registry]
url = "https://api.apr.dev"

[provider]
cluster = "devnet"
wallet = "~/.config/solana/id.json"

[scripts]
test = "yarn run ts-mocha -p ./tsconfig.json -t 1000000 tests/**/*.ts"
EOF

cat > "vessels/$VESSEL_NAME/scripts/launch.sh" << 'EOF'
#!/usr/bin/env bash
set -e

echo "🚀 Launching Vessel: Nebuchadnezzar"

nix develop --command bash << 'NIXEOF'

# Build
cd programs/tradewars-bbs
anchor build

# Deploy
anchor deploy

# Get program ID
PROGRAM_ID=$(solana-keygen pubkey target/deploy/tradewars_bbs-keypair.json)
echo "✅ Vessel deployed: $PROGRAM_ID"

NIXEOF
EOF

chmod +x "vessels/$VESSEL_NAME/scripts/launch.sh"

cat > "vessels/$VESSEL_NAME/README.md" << EOF
# Vessel: Nebuchadnezzar

**TradeWars BBS Deployment Vessel**

## Launch

\`\`\`bash
cd vessels/$VESSEL_NAME
nix develop
./scripts/launch.sh
\`\`\`

## Manifest

- **Name**: Nebuchadnezzar
- **Type**: Deployment Vessel
- **Network**: Solana Devnet
- **Cargo**: TradeWars BBS Program
- **Destination**: Sector 1

## Crew

- Captain: Your Wallet
- Credits: 1,000,000 SOL
- Status: Ready for Launch

🚢⚡
EOF

echo ""
echo "✅ Vessel Prepared: $VESSEL_NAME"
echo ""
echo "📋 Manifest:"
echo "  Location: vessels/$VESSEL_NAME"
echo "  Programs: TradeWars BBS"
echo "  Network: Solana Devnet"
echo "  Status: Ready"
echo ""
echo "🚀 Launch Commands:"
echo "  cd vessels/$VESSEL_NAME"
echo "  nix develop"
echo "  ./scripts/launch.sh"
echo ""
echo "🚢 Vessel ready for deployment!"
