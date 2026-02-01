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
