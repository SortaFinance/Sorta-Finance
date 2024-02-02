//! Program state processor

use crate::{
    self as vault_program,
    error::LendingError,
    instruction::LendingInstruction,
    math::{Decimal, TryAdd},
    oracles::get_pyth_price,
    state::{
        validate_reserve_config, InitLendingMarketParams, InitReserveParams,
        LendingMarket, NewReserveCollateralParams, NewReserveLiquidityParams, Reserve,
        ReserveCollateral, ReserveConfig, ReserveLiquidity,
    },
};
use bytemuck::bytes_of;
use pyth_sdk_solana::{self, state::ProductAccount};
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint::ProgramResult,
    instruction::{Instruction},
    msg,
    program::{invoke, invoke_signed},
    program_error::ProgramError,
    program_pack::{IsInitialized, Pack},
    pubkey::Pubkey,
    system_instruction::create_account,
    sysvar::{
        clock::{self, Clock},
        rent::Rent,
        Sysvar,
    },
};
use vault_sdk::state::{LendingMarketMetadata, RateLimiter, RateLimiterConfig};
use spl_token::state::Mint;
use std::{result::Result};

/// vault market owner
pub mod vault_market_owner {
    solana_program::declare_id!("5pHk2TmnqQzRF9L6egy5FfiyBgS7G9cMZ5RFaJAvghzw");
}

/// Processes an instruction
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    input: &[u8],
) -> ProgramResult {
    let instruction = LendingInstruction::unpack(input)?;
    match instruction {
        LendingInstruction::InitLendingMarket {
            owner,
            quote_currency,
        } => {
            msg!("Instruction: Init Lending Market");
            process_init_lending_market(program_id, owner, quote_currency, accounts)
        }
        LendingInstruction::SetLendingMarketOwnerAndConfig {
            new_owner,
            rate_limiter_config,
            whitelisted_liquidator,
            risk_authority,
        } => {
            msg!("Instruction: Set Lending Market Owner");
            process_set_lending_market_owner_and_config(
                program_id,
                new_owner,
                rate_limiter_config,
                whitelisted_liquidator,
                risk_authority,
                accounts,
            )
        }
        LendingInstruction::InitReserve {
            liquidity_amount,
            config,
        } => {
            msg!("Instruction: Init Reserve");
            process_init_reserve(program_id, liquidity_amount, config, accounts)
        }
        LendingInstruction::RefreshReserve => {
            msg!("Instruction: Refresh Reserve");
            process_refresh_reserve(program_id, accounts)
        }
        LendingInstruction::DepositReserveLiquidity { liquidity_amount } => {
            msg!("Instruction: Deposit Reserve Liquidity");
            process_deposit_reserve_liquidity(program_id, liquidity_amount, accounts)
        }
        LendingInstruction::RedeemReserveCollateral { collateral_amount } => {
            msg!("Instruction: Redeem Reserve Collateral");
            process_redeem_reserve_collateral(program_id, collateral_amount, accounts)
        }
        LendingInstruction::UpdateReserveConfig {
            config,
            rate_limiter_config,
        } => {
            msg!("Instruction: UpdateReserveConfig");
            process_update_reserve_config(program_id, config, rate_limiter_config, accounts)
        }
        LendingInstruction::RedeemFees => {
            msg!("Instruction: RedeemFees");
            process_redeem_fees(program_id, accounts)
        }
        LendingInstruction::UpdateMarketMetadata => {
            msg!("Instruction: Update Metadata");
            let metadata = LendingMarketMetadata::new_from_bytes(input)?;
            process_update_market_metadata(program_id, metadata, accounts)
        }
    }
}

fn process_init_lending_market(
    program_id: &Pubkey,
    owner: Pubkey,
    quote_currency: [u8; 32],
    accounts: &[AccountInfo],
) -> ProgramResult {
    let account_info_iter = &mut accounts.iter();
    let lending_market_info = next_account_info(account_info_iter)?;
    let rent = &Rent::from_account_info(next_account_info(account_info_iter)?)?;
    let token_program_id = next_account_info(account_info_iter)?;
    let oracle_program_id = next_account_info(account_info_iter)?;

    assert_rent_exempt(rent, lending_market_info)?;
    let mut lending_market = assert_uninitialized::<LendingMarket>(lending_market_info)?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }

    lending_market.init(InitLendingMarketParams {
        bump_seed: Pubkey::find_program_address(&[lending_market_info.key.as_ref()], program_id).1,
        owner,
        quote_currency,
        token_program_id: *token_program_id.key,
        oracle_program_id: *oracle_program_id.key,
    });
    LendingMarket::pack(lending_market, &mut lending_market_info.data.borrow_mut())?;

    Ok(())
}

#[inline(never)] // avoid stack frame limit
fn process_set_lending_market_owner_and_config(
    program_id: &Pubkey,
    new_owner: Pubkey,
    rate_limiter_config: RateLimiterConfig,
    whitelisted_liquidator: Option<Pubkey>,
    risk_authority: Pubkey,
    accounts: &[AccountInfo],
) -> ProgramResult {
    let account_info_iter = &mut accounts.iter();
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_owner_info = next_account_info(account_info_iter)?;

    let mut lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &lending_market.owner != lending_market_owner_info.key {
        msg!("Lending market owner does not match the lending market owner provided");
        return Err(LendingError::InvalidMarketOwner.into());
    }
    if !lending_market_owner_info.is_signer {
        msg!("Lending market owner provided must be a signer");
        return Err(LendingError::InvalidSigner.into());
    }

    lending_market.owner = new_owner;
    lending_market.risk_authority = risk_authority;

    if rate_limiter_config != lending_market.rate_limiter.config {
        lending_market.rate_limiter = RateLimiter::new(rate_limiter_config, Clock::get()?.slot);
    }

    lending_market.whitelisted_liquidator = whitelisted_liquidator;

    LendingMarket::pack(lending_market, &mut lending_market_info.data.borrow_mut())?;

    Ok(())
}

fn process_init_reserve(
    program_id: &Pubkey,
    liquidity_amount: u64,
    config: ReserveConfig,
    accounts: &[AccountInfo],
) -> ProgramResult {
    if liquidity_amount == 0 {
        msg!("Reserve must be initialized with liquidity");
        return Err(LendingError::InvalidAmount.into());
    }
    validate_reserve_config(config)?;
    let account_info_iter = &mut accounts.iter().peekable();
    let source_liquidity_info = next_account_info(account_info_iter)?;
    let destination_collateral_info = next_account_info(account_info_iter)?;
    let reserve_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_mint_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_supply_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_fee_receiver_info = next_account_info(account_info_iter)?;
    let reserve_collateral_mint_info = next_account_info(account_info_iter)?;
    let reserve_collateral_supply_info = next_account_info(account_info_iter)?;
    let pyth_product_info = next_account_info(account_info_iter)?;
    let pyth_price_info = next_account_info(account_info_iter)?;
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_authority_info = next_account_info(account_info_iter)?;
    let lending_market_owner_info = next_account_info(account_info_iter)?;
    let user_transfer_authority_info = next_account_info(account_info_iter)?;

    let clock = &Clock::get()?;
    if account_info_iter.peek().map(|a| a.key) == Some(&clock::ID) {
        next_account_info(account_info_iter)?;
    }

    let rent_info = next_account_info(account_info_iter)?;
    let rent = &Rent::from_account_info(rent_info)?;
    let token_program_id = next_account_info(account_info_iter)?;

    assert_rent_exempt(rent, reserve_info)?;
    let mut reserve = assert_uninitialized::<Reserve>(reserve_info)?;
    if reserve_info.owner != program_id {
        msg!(
            "Reserve provided is not owned by the lending program {} != {}",
            &reserve_info.owner.to_string(),
            &program_id.to_string(),
        );
        return Err(LendingError::InvalidAccountOwner.into());
    }

    if reserve_liquidity_supply_info.key == source_liquidity_info.key {
        msg!("Reserve liquidity supply cannot be used as the source liquidity provided");
        return Err(LendingError::InvalidAccountInput.into());
    }

    let lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!(
            "Lending market provided is not owned by the lending program  {} != {}",
            &lending_market_info.owner.to_string(),
            &program_id.to_string(),
        );
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &lending_market.token_program_id != token_program_id.key {
        msg!("Lending market token program does not match the token program provided");
        return Err(LendingError::InvalidTokenProgram.into());
    }
    if &lending_market.owner != lending_market_owner_info.key {
        msg!("Lending market owner does not match the lending market owner provided");
        return Err(LendingError::InvalidMarketOwner.into());
    }
    if !lending_market_owner_info.is_signer {
        msg!("Lending market owner provided must be a signer");
        return Err(LendingError::InvalidSigner.into());
    }
    if *pyth_price_info.key == vault_program::NULL_PUBKEY
            || *pyth_product_info.key == vault_program::NULL_PUBKEY
    {
        msg!("Both price oracles are null. At least one must be non-null");
        return Err(LendingError::InvalidOracleConfig.into());
    }
    validate_pyth_keys(&lending_market, pyth_product_info, pyth_price_info)?;

    let (market_price, smoothed_market_price) =
        get_price(pyth_price_info, clock)?;

    let authority_signer_seeds = &[
        lending_market_info.key.as_ref(),
        &[lending_market.bump_seed],
    ];
    let lending_market_authority_pubkey =
        Pubkey::create_program_address(authority_signer_seeds, program_id)?;
    if &lending_market_authority_pubkey != lending_market_authority_info.key {
        msg!(
            "Derived lending market authority does not match the lending market authority provided"
        );
        return Err(LendingError::InvalidMarketAuthority.into());
    }

    let reserve_liquidity_mint = unpack_mint(&reserve_liquidity_mint_info.data.borrow())?;
    if reserve_liquidity_mint_info.owner != token_program_id.key {
        msg!("Reserve liquidity mint is not owned by the token program provided");
        return Err(LendingError::InvalidTokenOwner.into());
    }

    reserve.init(InitReserveParams {
        current_slot: clock.slot,
        lending_market: *lending_market_info.key,
        liquidity: ReserveLiquidity::new(NewReserveLiquidityParams {
            mint_pubkey: *reserve_liquidity_mint_info.key,
            mint_decimals: reserve_liquidity_mint.decimals,
            supply_pubkey: *reserve_liquidity_supply_info.key,
            pyth_oracle_pubkey: *pyth_price_info.key,
            market_price,
            smoothed_market_price: smoothed_market_price.unwrap_or(market_price),
        }),
        collateral: ReserveCollateral::new(NewReserveCollateralParams {
            mint_pubkey: *reserve_collateral_mint_info.key,
            supply_pubkey: *reserve_collateral_supply_info.key,
        }),
        config,
        rate_limiter_config: RateLimiterConfig::default(),
    });

    let collateral_amount = reserve.deposit_liquidity(liquidity_amount)?;
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    spl_token_init_account(TokenInitializeAccountParams {
        account: reserve_liquidity_supply_info.clone(),
        mint: reserve_liquidity_mint_info.clone(),
        owner: lending_market_authority_info.clone(),
        rent: rent_info.clone(),
        token_program: token_program_id.clone(),
    })?;

    spl_token_init_account(TokenInitializeAccountParams {
        account: reserve_liquidity_fee_receiver_info.clone(),
        mint: reserve_liquidity_mint_info.clone(),
        owner: lending_market_authority_info.clone(),
        rent: rent_info.clone(),
        token_program: token_program_id.clone(),
    })?;

    spl_token_init_mint(TokenInitializeMintParams {
        mint: reserve_collateral_mint_info.clone(),
        authority: lending_market_authority_info.key,
        rent: rent_info.clone(),
        decimals: reserve_liquidity_mint.decimals,
        token_program: token_program_id.clone(),
    })?;

    spl_token_init_account(TokenInitializeAccountParams {
        account: reserve_collateral_supply_info.clone(),
        mint: reserve_collateral_mint_info.clone(),
        owner: lending_market_authority_info.clone(),
        rent: rent_info.clone(),
        token_program: token_program_id.clone(),
    })?;

    spl_token_init_account(TokenInitializeAccountParams {
        account: destination_collateral_info.clone(),
        mint: reserve_collateral_mint_info.clone(),
        owner: user_transfer_authority_info.clone(),
        rent: rent_info.clone(),
        token_program: token_program_id.clone(),
    })?;

    spl_token_transfer(TokenTransferParams {
        source: source_liquidity_info.clone(),
        destination: reserve_liquidity_supply_info.clone(),
        amount: liquidity_amount,
        authority: user_transfer_authority_info.clone(),
        authority_signer_seeds: &[],
        token_program: token_program_id.clone(),
    })?;

    spl_token_mint_to(TokenMintToParams {
        mint: reserve_collateral_mint_info.clone(),
        destination: destination_collateral_info.clone(),
        amount: collateral_amount,
        authority: lending_market_authority_info.clone(),
        authority_signer_seeds,
        token_program: token_program_id.clone(),
    })?;

    Ok(())
}

fn process_refresh_reserve(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
    let account_info_iter = &mut accounts.iter().peekable();
    let reserve_info = next_account_info(account_info_iter)?;
    let pyth_price_info = next_account_info(account_info_iter)?;
    let clock = &Clock::get()?;
    if account_info_iter.peek().map(|a| a.key) == Some(&clock::ID) {
        next_account_info(account_info_iter)?;
    }
    _refresh_reserve(
        program_id,
        reserve_info,
        pyth_price_info,
        clock,
    )
}

fn _refresh_reserve<'a>(
    program_id: &Pubkey,
    reserve_info: &AccountInfo<'a>,
    pyth_price_info: &AccountInfo<'a>,
    clock: &Clock,
) -> ProgramResult {
    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!("Reserve provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &reserve.liquidity.pyth_oracle_pubkey != pyth_price_info.key {
        msg!("Reserve liquidity pyth oracle does not match the reserve liquidity pyth oracle provided");
        return Err(LendingError::InvalidAccountInput.into());
    }

    let (market_price, smoothed_market_price) =
        get_price(pyth_price_info, clock)?;

    reserve.liquidity.market_price = market_price;

    if let Some(smoothed_market_price) = smoothed_market_price {
        reserve.liquidity.smoothed_market_price = smoothed_market_price;
    }

    if reserve.liquidity.pyth_oracle_pubkey == vault_program::NULL_PUBKEY {
        reserve.liquidity.smoothed_market_price = market_price;
    }

    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    _refresh_reserve_interest(program_id, reserve_info, clock)
}

/// Lite version of refresh_reserve that should be used when the oracle price doesn't need to be updated
/// BE CAREFUL WHEN USING THIS
fn _refresh_reserve_interest<'a>(
    program_id: &Pubkey,
    reserve_info: &AccountInfo<'a>,
    clock: &Clock,
) -> ProgramResult {
    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!("Reserve provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }

    reserve.accrue_interest(clock.slot)?;
    reserve.last_update.update_slot(clock.slot);
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    Ok(())
}

fn process_deposit_reserve_liquidity(
    program_id: &Pubkey,
    liquidity_amount: u64,
    accounts: &[AccountInfo],
) -> ProgramResult {
    if liquidity_amount == 0 {
        msg!("Liquidity amount provided cannot be zero");
        return Err(LendingError::InvalidAmount.into());
    }

    let account_info_iter = &mut accounts.iter().peekable();
    let source_liquidity_info = next_account_info(account_info_iter)?;
    let destination_collateral_info = next_account_info(account_info_iter)?;
    let reserve_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_supply_info = next_account_info(account_info_iter)?;
    let reserve_collateral_mint_info = next_account_info(account_info_iter)?;
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_authority_info = next_account_info(account_info_iter)?;
    let user_transfer_authority_info = next_account_info(account_info_iter)?;
    let clock = &Clock::get()?;
    if account_info_iter.peek().map(|a| a.key) == Some(&clock::ID) {
        next_account_info(account_info_iter)?;
    }
    let token_program_id = next_account_info(account_info_iter)?;

    _refresh_reserve_interest(program_id, reserve_info, clock)?;
    _deposit_reserve_liquidity(
        program_id,
        liquidity_amount,
        source_liquidity_info,
        destination_collateral_info,
        reserve_info,
        reserve_liquidity_supply_info,
        reserve_collateral_mint_info,
        lending_market_info,
        lending_market_authority_info,
        user_transfer_authority_info,
        clock,
        token_program_id,
    )?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn _deposit_reserve_liquidity<'a>(
    program_id: &Pubkey,
    liquidity_amount: u64,
    source_liquidity_info: &AccountInfo<'a>,
    destination_collateral_info: &AccountInfo<'a>,
    reserve_info: &AccountInfo<'a>,
    reserve_liquidity_supply_info: &AccountInfo<'a>,
    reserve_collateral_mint_info: &AccountInfo<'a>,
    lending_market_info: &AccountInfo<'a>,
    lending_market_authority_info: &AccountInfo<'a>,
    user_transfer_authority_info: &AccountInfo<'a>,
    clock: &Clock,
    token_program_id: &AccountInfo<'a>,
) -> Result<u64, ProgramError> {
    let lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &lending_market.token_program_id != token_program_id.key {
        msg!("Lending market token program does not match the token program provided");
        return Err(LendingError::InvalidTokenProgram.into());
    }
    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!("Reserve provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &reserve.lending_market != lending_market_info.key {
        msg!("Reserve lending market does not match the lending market provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.liquidity.supply_pubkey != reserve_liquidity_supply_info.key {
        msg!("Reserve liquidity supply does not match the reserve liquidity supply provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.collateral.mint_pubkey != reserve_collateral_mint_info.key {
        msg!("Reserve collateral mint does not match the reserve collateral mint provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.liquidity.supply_pubkey == source_liquidity_info.key {
        msg!("Reserve liquidity supply cannot be used as the source liquidity provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.collateral.supply_pubkey == destination_collateral_info.key {
        msg!("Reserve collateral supply cannot be used as the destination collateral provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if reserve.last_update.is_stale(clock.slot)? {
        msg!("Reserve is stale and must be refreshed in the current slot");
        return Err(LendingError::ReserveStale.into());
    }
    let authority_signer_seeds = &[
        lending_market_info.key.as_ref(),
        &[lending_market.bump_seed],
    ];
    let lending_market_authority_pubkey =
        Pubkey::create_program_address(authority_signer_seeds, program_id)?;
    if &lending_market_authority_pubkey != lending_market_authority_info.key {
        msg!(
            "Derived lending market authority {} does not match the lending market authority provided {}",
            &lending_market_authority_pubkey.to_string(),
            &lending_market_authority_info.key.to_string(),
        );
        return Err(LendingError::InvalidMarketAuthority.into());
    }

    if Decimal::from(liquidity_amount)
        .try_add(reserve.liquidity.total_supply()?)?
        .try_floor_u64()?
        > reserve.config.deposit_limit
    {
        msg!("Cannot deposit liquidity above the reserve deposit limit");
        return Err(LendingError::InvalidAmount.into());
    }

    let collateral_amount = reserve.deposit_liquidity(liquidity_amount)?;
    reserve.last_update.mark_stale();
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    spl_token_transfer(TokenTransferParams {
        source: source_liquidity_info.clone(),
        destination: reserve_liquidity_supply_info.clone(),
        amount: liquidity_amount,
        authority: user_transfer_authority_info.clone(),
        authority_signer_seeds: &[],
        token_program: token_program_id.clone(),
    })?;

    spl_token_mint_to(TokenMintToParams {
        mint: reserve_collateral_mint_info.clone(),
        destination: destination_collateral_info.clone(),
        amount: collateral_amount,
        authority: lending_market_authority_info.clone(),
        authority_signer_seeds,
        token_program: token_program_id.clone(),
    })?;

    Ok(collateral_amount)
}

fn process_redeem_reserve_collateral(
    program_id: &Pubkey,
    collateral_amount: u64,
    accounts: &[AccountInfo],
) -> ProgramResult {
    if collateral_amount == 0 {
        msg!("Collateral amount provided cannot be zero");
        return Err(LendingError::InvalidAmount.into());
    }

    let account_info_iter = &mut accounts.iter().peekable();
    let source_collateral_info = next_account_info(account_info_iter)?;
    let destination_liquidity_info = next_account_info(account_info_iter)?;
    let reserve_info = next_account_info(account_info_iter)?;
    let reserve_collateral_mint_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_supply_info = next_account_info(account_info_iter)?;
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_authority_info = next_account_info(account_info_iter)?;
    let user_transfer_authority_info = next_account_info(account_info_iter)?;
    let clock = &Clock::get()?;
    if account_info_iter.peek().map(|a| a.key) == Some(&clock::ID) {
        next_account_info(account_info_iter)?;
    }
    let token_program_id = next_account_info(account_info_iter)?;

    _redeem_reserve_collateral(
        program_id,
        collateral_amount,
        source_collateral_info,
        destination_liquidity_info,
        reserve_info,
        reserve_collateral_mint_info,
        reserve_liquidity_supply_info,
        lending_market_info,
        lending_market_authority_info,
        user_transfer_authority_info,
        clock,
        token_program_id,
        true,
    )?;
    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    reserve.last_update.mark_stale();
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn _redeem_reserve_collateral<'a>(
    program_id: &Pubkey,
    collateral_amount: u64,
    source_collateral_info: &AccountInfo<'a>,
    destination_liquidity_info: &AccountInfo<'a>,
    reserve_info: &AccountInfo<'a>,
    reserve_collateral_mint_info: &AccountInfo<'a>,
    reserve_liquidity_supply_info: &AccountInfo<'a>,
    lending_market_info: &AccountInfo<'a>,
    lending_market_authority_info: &AccountInfo<'a>,
    user_transfer_authority_info: &AccountInfo<'a>,
    clock: &Clock,
    token_program_id: &AccountInfo<'a>,
    check_rate_limits: bool,
) -> Result<u64, ProgramError> {
    let mut lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &lending_market.token_program_id != token_program_id.key {
        msg!("Lending market token program does not match the token program provided");
        return Err(LendingError::InvalidTokenProgram.into());
    }

    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!("Reserve provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &reserve.lending_market != lending_market_info.key {
        msg!("Reserve lending market does not match the lending market provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.collateral.mint_pubkey != reserve_collateral_mint_info.key {
        msg!("Reserve collateral mint does not match the reserve collateral mint provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.collateral.supply_pubkey == source_collateral_info.key {
        msg!("Reserve collateral supply cannot be used as the source collateral provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.liquidity.supply_pubkey != reserve_liquidity_supply_info.key {
        msg!("Reserve liquidity supply does not match the reserve liquidity supply provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.liquidity.supply_pubkey == destination_liquidity_info.key {
        msg!("Reserve liquidity supply cannot be used as the destination liquidity provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if reserve.last_update.is_stale(clock.slot)? {
        msg!("Reserve is stale and must be refreshed in the current slot");
        return Err(LendingError::ReserveStale.into());
    }

    let authority_signer_seeds = &[
        lending_market_info.key.as_ref(),
        &[lending_market.bump_seed],
    ];
    let lending_market_authority_pubkey =
        Pubkey::create_program_address(authority_signer_seeds, program_id)?;
    if &lending_market_authority_pubkey != lending_market_authority_info.key {
        msg!(
            "Derived lending market authority does not match the lending market authority provided"
        );
        return Err(LendingError::InvalidMarketAuthority.into());
    }

    let liquidity_amount = reserve.redeem_collateral(collateral_amount)?;

    if check_rate_limits {
        lending_market
            .rate_limiter
            .update(
                clock.slot,
                reserve.market_value_upper_bound(Decimal::from(liquidity_amount))?,
            )
            .map_err(|err| {
                msg!("Market outflow limit exceeded! Please try again later.");
                err
            })?;

        reserve
            .rate_limiter
            .update(clock.slot, Decimal::from(liquidity_amount))
            .map_err(|err| {
                msg!("Reserve outflow limit exceeded! Please try again later.");
                err
            })?;
    }

    reserve.last_update.mark_stale();
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;
    LendingMarket::pack(lending_market, &mut lending_market_info.data.borrow_mut())?;

    spl_token_burn(TokenBurnParams {
        mint: reserve_collateral_mint_info.clone(),
        source: source_collateral_info.clone(),
        amount: collateral_amount,
        authority: user_transfer_authority_info.clone(),
        authority_signer_seeds: &[],
        token_program: token_program_id.clone(),
    })?;

    spl_token_transfer(TokenTransferParams {
        source: reserve_liquidity_supply_info.clone(),
        destination: destination_liquidity_info.clone(),
        amount: liquidity_amount,
        authority: lending_market_authority_info.clone(),
        authority_signer_seeds,
        token_program: token_program_id.clone(),
    })?;

    Ok(liquidity_amount)
}

#[inline(never)] // avoid stack frame limit
fn process_update_reserve_config(
    program_id: &Pubkey,
    config: ReserveConfig,
    rate_limiter_config: RateLimiterConfig,
    accounts: &[AccountInfo],
) -> ProgramResult {
    validate_reserve_config(config)?;
    let account_info_iter = &mut accounts.iter();
    let reserve_info = next_account_info(account_info_iter)?;
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_authority_info = next_account_info(account_info_iter)?;
    let signer_info = next_account_info(account_info_iter)?;
    let pyth_product_info = next_account_info(account_info_iter)?;
    let pyth_price_info = next_account_info(account_info_iter)?;

    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!(
            "Reserve provided is not owned by the lending program {} != {}",
            &reserve_info.owner.to_string(),
            &program_id.to_string(),
        );
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &reserve.lending_market != lending_market_info.key {
        msg!("Reserve lending market does not match the lending market provided");
        return Err(LendingError::InvalidAccountInput.into());
    }

    let lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!(
            "Lending market provided is not owned by the lending program  {} != {}",
            &lending_market_info.owner.to_string(),
            &program_id.to_string(),
        );
        return Err(LendingError::InvalidAccountOwner.into());
    }

    // if it's a permissionless market
    if &vault_market_owner::id() != signer_info.key {
        if reserve.config.protocol_liquidation_fee != config.protocol_liquidation_fee {
            msg!("permissionless markets can't edit protocol liquidation fees");
            return Err(LendingError::InvalidConfig.into());
        }
        if reserve.config.protocol_take_rate != config.protocol_take_rate {
            msg!("permissionless markets can't edit protocol take rate");
            return Err(LendingError::InvalidConfig.into());
        }
        if reserve.config.fee_receiver != config.fee_receiver {
            msg!("permissionless markets can't edit fee receiver");
            return Err(LendingError::InvalidConfig.into());
        }
        if reserve.config.fees != config.fees {
            msg!("permissionless markets can't edit fee configs!");
            return Err(LendingError::InvalidConfig.into());
        }
    }

    let authority_signer_seeds = &[
        lending_market_info.key.as_ref(),
        &[lending_market.bump_seed],
    ];

    let lending_market_authority_pubkey =
        Pubkey::create_program_address(authority_signer_seeds, program_id)?;
    if &lending_market_authority_pubkey != lending_market_authority_info.key {
        msg!(
            "Derived lending market authority does not match the lending market authority provided"
        );
        return Err(LendingError::InvalidMarketAuthority.into());
    }

    if !signer_info.is_signer {
        msg!("Lending market owner or risk authority provided must be a signer");
        return Err(LendingError::InvalidSigner.into());
    }

    if signer_info.key == &lending_market.owner {
        // if window duration or max outflow are different, then create a new rate limiter instance.
        if rate_limiter_config != reserve.rate_limiter.config {
            reserve.rate_limiter = RateLimiter::new(rate_limiter_config, Clock::get()?.slot);
        }

        if *pyth_price_info.key != reserve.liquidity.pyth_oracle_pubkey {
            validate_pyth_keys(&lending_market, pyth_product_info, pyth_price_info)?;
            reserve.liquidity.pyth_oracle_pubkey = *pyth_price_info.key;
        }

        if reserve.liquidity.pyth_oracle_pubkey == vault_program::NULL_PUBKEY
        {
            msg!("At least one price oracle must have a non-null pubkey");
            return Err(LendingError::InvalidOracleConfig.into());
        }

        reserve.config = config;
    } else if signer_info.key == &lending_market.risk_authority {
        // only can disable outflows
        if rate_limiter_config.window_duration > 0 && rate_limiter_config.max_outflow == 0 {
            reserve.rate_limiter = RateLimiter::new(rate_limiter_config, Clock::get()?.slot);
        }

        // only certain reserve config fields can be changed by the risk authority, and only in the
        // safer direction for now
        if config.borrow_limit < reserve.config.borrow_limit {
            reserve.config.borrow_limit = config.borrow_limit;
        }

        if config.deposit_limit < reserve.config.deposit_limit {
            reserve.config.deposit_limit = config.deposit_limit;
        }
    } else if *signer_info.key == vault_market_owner::id()
    // 5ph has the ability to change the
    // fees on permissionless markets
    {
        reserve.config.fees = config.fees;
        reserve.config.protocol_liquidation_fee = config.protocol_liquidation_fee;
        reserve.config.protocol_take_rate = config.protocol_take_rate;
        reserve.config.fee_receiver = config.fee_receiver;
    } else {
        msg!("Signer must be the Lending market owner or risk authority");
        return Err(LendingError::InvalidSigner.into());
    }

    reserve.last_update.mark_stale();
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;
    Ok(())
}

#[inline(never)] // avoid stack frame limit
fn process_redeem_fees(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
    let account_info_iter = &mut accounts.iter().peekable();
    let reserve_info = next_account_info(account_info_iter)?;
    let reserve_liquidity_fee_receiver_info = next_account_info(account_info_iter)?;
    let reserve_supply_liquidity_info = next_account_info(account_info_iter)?;
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_authority_info = next_account_info(account_info_iter)?;
    let token_program_id = next_account_info(account_info_iter)?;
    let clock = &Clock::get()?;

    let mut reserve = Reserve::unpack(&reserve_info.data.borrow())?;
    if reserve_info.owner != program_id {
        msg!(
            "Reserve provided is not owned by the lending program {} != {}",
            &reserve_info.owner.to_string(),
            &program_id.to_string(),
        );
        return Err(LendingError::InvalidAccountOwner.into());
    }

    if &reserve.config.fee_receiver != reserve_liquidity_fee_receiver_info.key {
        msg!("Reserve liquidity fee receiver does not match the reserve liquidity fee receiver provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.liquidity.supply_pubkey != reserve_supply_liquidity_info.key {
        msg!("Reserve liquidity supply must be used as the reserve supply liquidity provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if &reserve.lending_market != lending_market_info.key {
        msg!("Reserve lending market does not match the lending market provided");
        return Err(LendingError::InvalidAccountInput.into());
    }
    if reserve.last_update.is_stale(clock.slot)? {
        msg!("reserve is stale and must be refreshed in the current slot");
        return Err(LendingError::ReserveStale.into());
    }

    let lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }
    if &lending_market.token_program_id != token_program_id.key {
        msg!("Lending market token program does not match the token program provided");
        return Err(LendingError::InvalidTokenProgram.into());
    }
    let authority_signer_seeds = &[
        lending_market_info.key.as_ref(),
        &[lending_market.bump_seed],
    ];
    let lending_market_authority_pubkey =
        Pubkey::create_program_address(authority_signer_seeds, program_id)?;
    if &lending_market_authority_pubkey != lending_market_authority_info.key {
        msg!(
            "Derived lending market authority does not match the lending market authority provided"
        );
        return Err(LendingError::InvalidMarketAuthority.into());
    }

    let withdraw_amount = reserve.calculate_redeem_fees()?;
    if withdraw_amount == 0 {
        return Err(LendingError::InsufficientProtocolFeesToRedeem.into());
    }

    reserve.liquidity.redeem_fees(withdraw_amount)?;
    reserve.last_update.mark_stale();
    Reserve::pack(reserve, &mut reserve_info.data.borrow_mut())?;

    spl_token_transfer(TokenTransferParams {
        source: reserve_supply_liquidity_info.clone(),
        destination: reserve_liquidity_fee_receiver_info.clone(),
        amount: withdraw_amount,
        authority: lending_market_authority_info.clone(),
        authority_signer_seeds,
        token_program: token_program_id.clone(),
    })?;

    Ok(())
}

fn assert_rent_exempt(rent: &Rent, account_info: &AccountInfo) -> ProgramResult {
    if !rent.is_exempt(account_info.lamports(), account_info.data_len()) {
        msg!(
            "Rent exempt balance insufficient got {} expected {}",
            &account_info.lamports().to_string(),
            &rent.minimum_balance(account_info.data_len()).to_string(),
        );
        Err(LendingError::NotRentExempt.into())
    } else {
        Ok(())
    }
}

fn process_update_market_metadata(
    program_id: &Pubkey,
    metadata: &LendingMarketMetadata,
    accounts: &[AccountInfo],
) -> Result<(), ProgramError> {
    let account_info_iter = &mut accounts.iter();
    let lending_market_info = next_account_info(account_info_iter)?;
    let lending_market_owner_info = next_account_info(account_info_iter)?;
    let metadata_info = next_account_info(account_info_iter)?;

    let lending_market = LendingMarket::unpack(&lending_market_info.data.borrow())?;
    if lending_market_info.owner != program_id {
        msg!("Lending market provided is not owned by the lending program",);
        return Err(LendingError::InvalidAccountOwner.into());
    }

    if &lending_market.owner != lending_market_owner_info.key {
        msg!("Lending market owner does not match the lending market owner provided");
        return Err(LendingError::InvalidMarketOwner.into());
    }

    if !lending_market_owner_info.is_signer {
        msg!("Lending market owner provided must be a signer");
        return Err(LendingError::InvalidSigner.into());
    }

    let metadata_seeds = &[lending_market_info.key.as_ref(), b"MetaData"];
    let (metadata_key, bump_seed) = Pubkey::find_program_address(metadata_seeds, program_id);
    if metadata_key != *metadata_info.key {
        msg!("Provided metadata account does not match the expected derived address");
        return Err(LendingError::InvalidAccountInput.into());
    }

    if bump_seed != metadata.bump_seed {
        msg!("Provided bump seed does not match the expected derived bump seed");
        return Err(LendingError::InvalidAmount.into());
    }

    // initialize
    if metadata_info.data_is_empty() {
        msg!("Creating metadata account");

        invoke_signed(
            &create_account(
                lending_market_owner_info.key,
                metadata_info.key,
                Rent::get()?.minimum_balance(std::mem::size_of::<LendingMarketMetadata>()),
                std::mem::size_of::<LendingMarketMetadata>() as u64,
                program_id,
            ),
            &[lending_market_owner_info.clone(), metadata_info.clone()],
            &[&[lending_market_info.key.as_ref(), br"MetaData", &[bump_seed]]],
        )?;
    }

    if metadata_info.owner != program_id {
        msg!("Metadata provided is not owned by the lending program");
        return Err(LendingError::InvalidAccountOwner.into());
    }

    let mut metadata_account_data = metadata_info.try_borrow_mut_data()?;
    metadata_account_data.copy_from_slice(bytes_of(metadata));

    Ok(())
}

fn assert_uninitialized<T: Pack + IsInitialized>(
    account_info: &AccountInfo,
) -> Result<T, ProgramError> {
    let account: T = T::unpack_unchecked(&account_info.data.borrow())?;
    if account.is_initialized() {
        Err(LendingError::AlreadyInitialized.into())
    } else {
        Ok(account)
    }
}

/// Unpacks a spl_token `Mint`.
fn unpack_mint(data: &[u8]) -> Result<Mint, LendingError> {
    Mint::unpack(data).map_err(|_| LendingError::InvalidTokenMint)
}

fn get_pyth_product_quote_currency(
    pyth_product: &ProductAccount,
) -> Result<[u8; 32], ProgramError> {
    pyth_product
        .iter()
        .find_map(|(key, val)| {
            if key == "quote_currency" {
                let mut value = [0u8; 32];
                value[0..val.len()].copy_from_slice(val.as_bytes());
                Some(value)
            } else {
                None
            }
        })
        .ok_or_else(|| {
            msg!("Pyth product quote currency not found");
            LendingError::InvalidOracleConfig.into()
        })
}

/// get_price tries to load the oracle price from pyth
fn get_price(
    pyth_price_account_info: &AccountInfo,
    clock: &Clock,
) -> Result<(Decimal, Option<Decimal>), ProgramError> {
    if let Ok(prices) = get_pyth_price(pyth_price_account_info, clock) {
        return Ok((prices.0, Some(prices.1)));
    }

    Err(LendingError::InvalidOracleConfig.into())
}

/// Issue a spl_token `InitializeAccount` instruction.
#[inline(always)]
fn spl_token_init_account(params: TokenInitializeAccountParams<'_>) -> ProgramResult {
    let TokenInitializeAccountParams {
        account,
        mint,
        owner,
        rent,
        token_program,
    } = params;
    let ix = spl_token::instruction::initialize_account(
        token_program.key,
        account.key,
        mint.key,
        owner.key,
    )?;
    let result = invoke(&ix, &[account, mint, owner, rent, token_program]);
    result.map_err(|_| LendingError::TokenInitializeAccountFailed.into())
}

/// Issue a spl_token `InitializeMint` instruction.
#[inline(always)]
fn spl_token_init_mint(params: TokenInitializeMintParams<'_, '_>) -> ProgramResult {
    let TokenInitializeMintParams {
        mint,
        rent,
        authority,
        token_program,
        decimals,
    } = params;
    let ix = spl_token::instruction::initialize_mint(
        token_program.key,
        mint.key,
        authority,
        None,
        decimals,
    )?;
    let result = invoke(&ix, &[mint, rent, token_program]);
    result.map_err(|_| LendingError::TokenInitializeMintFailed.into())
}

/// Invoke signed unless signers seeds are empty
#[inline(always)]
fn invoke_optionally_signed(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    authority_signer_seeds: &[&[u8]],
) -> ProgramResult {
    if authority_signer_seeds.is_empty() {
        invoke(instruction, account_infos)
    } else {
        invoke_signed(instruction, account_infos, &[authority_signer_seeds])
    }
}

/// Issue a spl_token `Transfer` instruction.
#[inline(always)]
fn spl_token_transfer(params: TokenTransferParams<'_, '_>) -> ProgramResult {
    let TokenTransferParams {
        source,
        destination,
        authority,
        token_program,
        amount,
        authority_signer_seeds,
    } = params;
    let result = invoke_optionally_signed(
        &spl_token::instruction::transfer(
            token_program.key,
            source.key,
            destination.key,
            authority.key,
            &[],
            amount,
        )?,
        &[source, destination, authority, token_program],
        authority_signer_seeds,
    );

    result.map_err(|_| LendingError::TokenTransferFailed.into())
}

/// Issue a spl_token `MintTo` instruction.
fn spl_token_mint_to(params: TokenMintToParams<'_, '_>) -> ProgramResult {
    let TokenMintToParams {
        mint,
        destination,
        authority,
        token_program,
        amount,
        authority_signer_seeds,
    } = params;
    let result = invoke_optionally_signed(
        &spl_token::instruction::mint_to(
            token_program.key,
            mint.key,
            destination.key,
            authority.key,
            &[],
            amount,
        )?,
        &[mint, destination, authority, token_program],
        authority_signer_seeds,
    );
    result.map_err(|_| LendingError::TokenMintToFailed.into())
}

/// Issue a spl_token `Burn` instruction.
#[inline(always)]
fn spl_token_burn(params: TokenBurnParams<'_, '_>) -> ProgramResult {
    let TokenBurnParams {
        mint,
        source,
        authority,
        token_program,
        amount,
        authority_signer_seeds,
    } = params;
    let result = invoke_optionally_signed(
        &spl_token::instruction::burn(
            token_program.key,
            source.key,
            mint.key,
            authority.key,
            &[],
            amount,
        )?,
        &[source, mint, authority, token_program],
        authority_signer_seeds,
    );
    result.map_err(|_| LendingError::TokenBurnFailed.into())
}

/// validates pyth AccountInfos
#[inline(always)]
fn validate_pyth_keys(
    lending_market: &LendingMarket,
    pyth_product_info: &AccountInfo,
    pyth_price_info: &AccountInfo,
) -> ProgramResult {
    if *pyth_price_info.key == vault_program::NULL_PUBKEY {
        return Ok(());
    }
    if &lending_market.oracle_program_id != pyth_product_info.owner {
        msg!("Pyth product account provided is not owned by the lending market oracle program");
        return Err(LendingError::InvalidOracleConfig.into());
    }
    if &lending_market.oracle_program_id != pyth_price_info.owner {
        msg!("Pyth price account provided is not owned by the lending market oracle program");
        return Err(LendingError::InvalidOracleConfig.into());
    }

    let pyth_product_data = pyth_product_info.try_borrow_data()?;
    let pyth_product = pyth_sdk_solana::state::load_product_account(&pyth_product_data)?;

    if &pyth_product.px_acc != pyth_price_info.key {
        msg!("Pyth product price account does not match the Pyth price provided");
        return Err(LendingError::InvalidOracleConfig.into());
    }

    let quote_currency = get_pyth_product_quote_currency(pyth_product)?;
    if lending_market.quote_currency != quote_currency {
        msg!("Lending market quote currency does not match the oracle quote currency");
        return Err(LendingError::InvalidOracleConfig.into());
    }
    Ok(())
}

struct TokenInitializeMintParams<'a: 'b, 'b> {
    mint: AccountInfo<'a>,
    rent: AccountInfo<'a>,
    authority: &'b Pubkey,
    decimals: u8,
    token_program: AccountInfo<'a>,
}

struct TokenInitializeAccountParams<'a> {
    account: AccountInfo<'a>,
    mint: AccountInfo<'a>,
    owner: AccountInfo<'a>,
    rent: AccountInfo<'a>,
    token_program: AccountInfo<'a>,
}

struct TokenTransferParams<'a: 'b, 'b> {
    source: AccountInfo<'a>,
    destination: AccountInfo<'a>,
    amount: u64,
    authority: AccountInfo<'a>,
    authority_signer_seeds: &'b [&'b [u8]],
    token_program: AccountInfo<'a>,
}

struct TokenMintToParams<'a: 'b, 'b> {
    mint: AccountInfo<'a>,
    destination: AccountInfo<'a>,
    amount: u64,
    authority: AccountInfo<'a>,
    authority_signer_seeds: &'b [&'b [u8]],
    token_program: AccountInfo<'a>,
}

struct TokenBurnParams<'a: 'b, 'b> {
    mint: AccountInfo<'a>,
    source: AccountInfo<'a>,
    amount: u64,
    authority: AccountInfo<'a>,
    authority_signer_seeds: &'b [&'b [u8]],
    token_program: AccountInfo<'a>,
}
