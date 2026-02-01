use anchor_lang::prelude::*;

declare_id!("StEg0RdFa1111111111111111111111111111111111");

#[program]
pub mod stego_lifting {
    use super::*;

    pub fn lift(ctx: Context<Lift>, shard: u8, data: Vec<u8>) -> Result<()> {
        let base = 1_000_000_000;
        let encoded = encode(shard, &data);
        
        let ix = anchor_lang::solana_program::system_instruction::transfer(
            &ctx.accounts.from.key(),
            &ctx.accounts.to.key(),
            base + encoded,
        );
        
        anchor_lang::solana_program::program::invoke(
            &ix,
            &[ctx.accounts.from.to_account_info(), ctx.accounts.to.to_account_info()],
        )?;
        
        emit!(Lifted { shard, gen: data[0], amount: base + encoded });
        Ok(())
    }
}

fn encode(shard: u8, data: &[u8]) -> u64 {
    let mut e = shard as u64;
    e |= (data.get(0).unwrap_or(&0) as u64) << 8;
    for (i, b) in data.iter().skip(1).take(4).enumerate() {
        e |= (*b as u64) << (16 + i * 8);
    }
    e
}

#[derive(Accounts)]
pub struct Lift<'info> {
    #[account(mut)]
    pub from: Signer<'info>,
    /// CHECK: Any recipient
    pub to: AccountInfo<'info>,
    pub system_program: Program<'info, System>,
}

#[event]
pub struct Lifted { pub shard: u8, pub gen: u8, pub amount: u64 }
