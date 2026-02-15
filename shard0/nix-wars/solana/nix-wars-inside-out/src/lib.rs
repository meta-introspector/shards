use anchor_lang::prelude::*;

declare_id!("NixWars11111111111111111111111111111111111");

#[program]
pub mod nix_wars_inside_out {
    use super::*;

    pub fn submit_move(
        ctx: Context<SubmitMove>,
        commitment: [u8; 32],
        zkperf_cycles: u64,
        from_sector: u8,
        to_sector: u8,
    ) -> Result<()> {
        let game_state = &mut ctx.accounts.game_state;
        
        // Store move on-chain (inside Solana)
        game_state.commitment = commitment;
        game_state.zkperf_cycles = zkperf_cycles;
        game_state.from_sector = from_sector;
        game_state.to_sector = to_sector;
        game_state.timestamp = Clock::get()?.unix_timestamp;
        
        // But the REAL game state lives off-chain in Nix derivations
        // Solana is just the witness ledger
        
        Ok(())
    }

    pub fn verify_consensus(
        ctx: Context<VerifyConsensus>,
        chosen_commitment: [u8; 32],
        rejected_commitment: [u8; 32],
        votes: u8,
    ) -> Result<()> {
        let consensus = &mut ctx.accounts.consensus;
        
        require!(votes >= 2, ErrorCode::InsufficientVotes);
        
        consensus.chosen = chosen_commitment;
        consensus.rejected = rejected_commitment;
        consensus.votes = votes;
        consensus.timestamp = Clock::get()?.unix_timestamp;
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct SubmitMove<'info> {
    #[account(init_if_needed, payer = player, space = 8 + GameState::SIZE)]
    pub game_state: Account<'info, GameState>,
    #[account(mut)]
    pub player: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct VerifyConsensus<'info> {
    #[account(init_if_needed, payer = authority, space = 8 + Consensus::SIZE)]
    pub consensus: Account<'info, Consensus>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct GameState {
    pub commitment: [u8; 32],
    pub zkperf_cycles: u64,
    pub from_sector: u8,
    pub to_sector: u8,
    pub timestamp: i64,
}

impl GameState {
    const SIZE: usize = 32 + 8 + 1 + 1 + 8;
}

#[account]
pub struct Consensus {
    pub chosen: [u8; 32],
    pub rejected: [u8; 32],
    pub votes: u8,
    pub timestamp: i64,
}

impl Consensus {
    const SIZE: usize = 32 + 32 + 1 + 8;
}

#[error_code]
pub enum ErrorCode {
    #[msg("Insufficient votes for consensus")]
    InsufficientVotes,
}
