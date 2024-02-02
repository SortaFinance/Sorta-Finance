//! Instruction types

use crate::state::{LendingMarketMetadata, ReserveType};
use crate::{
    error::LendingError,
    state::{RateLimiterConfig, ReserveConfig, ReserveFees},
};
use bytemuck::bytes_of;

use num_traits::FromPrimitive;
use solana_program::system_program;
use solana_program::{
    instruction::{AccountMeta, Instruction},
    msg,
    program_error::ProgramError,
    pubkey::{Pubkey, PUBKEY_BYTES},
    sysvar,
};
use std::{convert::TryInto, mem::size_of};

/// Instructions supported by the lending program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LendingInstruction {
    /// Initializes a new lending market.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Lending market account - uninitialized.
    ///   1. `[]` Rent sysvar.
    ///   2. `[]` Token program id.
    ///   3. `[]` Oracle program id.
    InitLendingMarket {
        /// Owner authority which can add new reserves
        owner: Pubkey,
        /// Currency market prices are quoted in
        /// e.g. "USD" null padded (`*b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"`) or SPL token mint pubkey
        quote_currency: [u8; 32],
    },

    /// Sets the new owner of a lending market.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Lending market account.
    ///   1. `[signer]` Current owner.
    SetLendingMarketOwnerAndConfig {
        /// The new owner
        new_owner: Pubkey,
        /// The new config
        rate_limiter_config: RateLimiterConfig,
        /// whitelist liquidator
        whitelisted_liquidator: Option<Pubkey>,
        /// The risk authority
        risk_authority: Pubkey,
    },

    /// Initializes a new lending market reserve.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Source liquidity token account.
    ///                     $authority can transfer $liquidity_amount.
    ///   1. `[writable]` Destination collateral token account - uninitialized.
    ///   2. `[writable]` Reserve account - uninitialized.
    ///   3. `[]` Reserve liquidity SPL Token mint.
    ///   4. `[writable]` Reserve liquidity supply SPL Token account - uninitialized.
    ///   5. `[writable]` Reserve liquidity fee receiver - uninitialized.
    ///   6. `[writable]` Reserve collateral SPL Token mint - uninitialized.
    ///   7 `[writable]` Reserve collateral token supply - uninitialized.
    ///   8. `[]` Pyth product account.
    ///   9. `[]` Pyth price account.
    ///             This will be used as the reserve liquidity oracle account.
    ///   10 `[]` Lending market account.
    ///   11 `[]` Derived lending market authority.
    ///   12 `[signer]` Lending market owner.
    ///   13 `[signer]` User transfer authority ($authority).
    ///   14 `[]` Clock sysvar (optional, will be removed soon).
    ///   15 `[]` Rent sysvar.
    ///   16 `[]` Token program id.
    InitReserve {
        /// Initial amount of liquidity to deposit into the new reserve
        liquidity_amount: u64,
        /// Reserve configuration values
        config: ReserveConfig,
    },

    /// Accrue interest and update market price of liquidity on a reserve.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Reserve account.
    ///   1. `[]` Pyth Reserve liquidity oracle account.
    ///             Must be the Pyth price account specified at InitReserve.
    ///   2. `[]` Clock sysvar (optional, will be removed soon).
    RefreshReserve,

    /// Deposit liquidity into a reserve in exchange for collateral. Collateral represents a share
    /// of the reserve liquidity pool.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Source liquidity token account.
    ///                     $authority can transfer $liquidity_amount.
    ///   1. `[writable]` Destination collateral token account.
    ///   2. `[writable]` Reserve account.
    ///   3. `[writable]` Reserve liquidity supply SPL Token account.
    ///   4. `[writable]` Reserve collateral SPL Token mint.
    ///   5. `[]` Lending market account.
    ///   6. `[]` Derived lending market authority.
    ///   7. `[signer]` User transfer authority ($authority).
    ///   8. `[]` Clock sysvar (optional, will be removed soon).
    ///   9. `[]` Token program id.
    DepositReserveLiquidity {
        /// Amount of liquidity to deposit in exchange for collateral tokens
        liquidity_amount: u64,
    },

    /// Redeem collateral from a reserve in exchange for liquidity.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` Source collateral token account.
    ///                     $authority can transfer $collateral_amount.
    ///   1. `[writable]` Destination liquidity token account.
    ///   2. `[writable]` Reserve account.
    ///   3. `[writable]` Reserve collateral SPL Token mint.
    ///   4. `[writable]` Reserve liquidity supply SPL Token account.
    ///   5. `[]` Lending market account.
    ///   6. `[]` Derived lending market authority.
    ///   7. `[signer]` User transfer authority ($authority).
    ///   8. `[]` Clock sysvar (optional, will be removed soon).
    ///   9. `[]` Token program id.
    RedeemReserveCollateral {
        /// Amount of collateral tokens to redeem in exchange for liquidity
        collateral_amount: u64,
    },

    /// Updates a reserves config and a reserve price oracle pubkeys
    ///
    /// Accounts expected by this instruction:
    ///
    ///   1. `[writable]` Reserve account - refreshed
    ///   2 `[]` Lending market account.
    ///   3 `[]` Derived lending market authority.
    ///   4 `[signer]` Lending market owner.
    ///   5 `[]` Pyth product key.
    ///   6 `[]` Pyth price key.
    UpdateReserveConfig {
        /// Reserve config to update to
        config: ReserveConfig,
        /// Rate limiter config
        rate_limiter_config: RateLimiterConfig,
    },

    ///   0. `[writable]` Reserve account.
    ///   1. `[writable]` Borrow reserve liquidity fee receiver account.
    ///                     Must be the fee account specified at InitReserve.
    ///   2. `[writable]` Reserve liquidity supply SPL Token account.
    ///   3. `[]` Lending market account.
    ///   4. `[]` Derived lending market authority.
    ///   5. `[]` Token program id.
    RedeemFees,

    /// UpdateMarketMetadata
    ///
    /// Accounts expected by this instruction:
    /// 0. `[]` Lending market account.
    /// 1. `[signer]` Lending market owner.
    /// 2. `[writable]` Lending market metadata account.
    /// Must be a pda with seeds [lending_market, "MetaData"]
    /// 3. `[]` System program
    UpdateMarketMetadata,
}

impl LendingInstruction {
    /// Unpacks a byte buffer into a [LendingInstruction](enum.LendingInstruction.html).
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (&tag, rest) = input
            .split_first()
            .ok_or(LendingError::InstructionUnpackError)?;
        Ok(match tag {
            0 => {
                let (owner, rest) = Self::unpack_pubkey(rest)?;
                let (quote_currency, _rest) = Self::unpack_bytes32(rest)?;
                Self::InitLendingMarket {
                    owner,
                    quote_currency: *quote_currency,
                }
            }
            1 => {
                let (new_owner, rest) = Self::unpack_pubkey(rest)?;
                let (window_duration, rest) = Self::unpack_u64(rest)?;
                let (max_outflow, rest) = Self::unpack_u64(rest)?;
                let (whitelisted_liquidator, rest) = match Self::unpack_u8(rest)? {
                    (0, rest) => (None, rest),
                    (1, rest) => {
                        let (pubkey, rest) = Self::unpack_pubkey(rest)?;
                        (Some(pubkey), rest)
                    }
                    _ => return Err(LendingError::InstructionUnpackError.into()),
                };

                let (risk_authority, _rest) = Self::unpack_pubkey(rest)?;
                Self::SetLendingMarketOwnerAndConfig {
                    new_owner,
                    rate_limiter_config: RateLimiterConfig {
                        window_duration,
                        max_outflow,
                    },
                    whitelisted_liquidator,
                    risk_authority,
                }
            }
            2 => {
                let (liquidity_amount, rest) = Self::unpack_u64(rest)?;
                let (optimal_utilization_rate, rest) = Self::unpack_u8(rest)?;
                let (max_utilization_rate, rest) = Self::unpack_u8(rest)?;
                let (loan_to_value_ratio, rest) = Self::unpack_u8(rest)?;
                let (liquidation_bonus, rest) = Self::unpack_u8(rest)?;
                let (liquidation_threshold, rest) = Self::unpack_u8(rest)?;
                let (min_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (optimal_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (max_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (super_max_borrow_rate, rest) = Self::unpack_u64(rest)?;
                let (borrow_fee_wad, rest) = Self::unpack_u64(rest)?;
                let (flash_loan_fee_wad, rest) = Self::unpack_u64(rest)?;
                let (host_fee_percentage, rest) = Self::unpack_u8(rest)?;
                let (deposit_limit, rest) = Self::unpack_u64(rest)?;
                let (borrow_limit, rest) = Self::unpack_u64(rest)?;
                let (fee_receiver, rest) = Self::unpack_pubkey(rest)?;
                let (protocol_liquidation_fee, rest) = Self::unpack_u8(rest)?;
                let (protocol_take_rate, rest) = Self::unpack_u8(rest)?;
                let (added_borrow_weight_bps, rest) = Self::unpack_u64(rest)?;
                let (asset_type, rest) = Self::unpack_u8(rest)?;
                let (max_liquidation_bonus, rest) = Self::unpack_u8(rest)?;
                let (max_liquidation_threshold, _rest) = Self::unpack_u8(rest)?;
                Self::InitReserve {
                    liquidity_amount,
                    config: ReserveConfig {
                        optimal_utilization_rate,
                        max_utilization_rate,
                        loan_to_value_ratio,
                        liquidation_bonus,
                        max_liquidation_bonus,
                        liquidation_threshold,
                        max_liquidation_threshold,
                        min_borrow_rate,
                        optimal_borrow_rate,
                        max_borrow_rate,
                        super_max_borrow_rate,
                        fees: ReserveFees {
                            borrow_fee_wad,
                            flash_loan_fee_wad,
                            host_fee_percentage,
                        },
                        deposit_limit,
                        borrow_limit,
                        fee_receiver,
                        protocol_liquidation_fee,
                        protocol_take_rate,
                        added_borrow_weight_bps,
                        reserve_type: ReserveType::from_u8(asset_type).unwrap(),
                    },
                }
            }
            3 => Self::RefreshReserve,
            4 => {
                let (liquidity_amount, _rest) = Self::unpack_u64(rest)?;
                Self::DepositReserveLiquidity { liquidity_amount }
            }
            5 => {
                let (collateral_amount, _rest) = Self::unpack_u64(rest)?;
                Self::RedeemReserveCollateral { collateral_amount }
            }
            6 => {
                let (optimal_utilization_rate, rest) = Self::unpack_u8(rest)?;
                let (max_utilization_rate, rest) = Self::unpack_u8(rest)?;
                let (loan_to_value_ratio, rest) = Self::unpack_u8(rest)?;
                let (liquidation_bonus, rest) = Self::unpack_u8(rest)?;
                let (liquidation_threshold, rest) = Self::unpack_u8(rest)?;
                let (min_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (optimal_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (max_borrow_rate, rest) = Self::unpack_u8(rest)?;
                let (super_max_borrow_rate, rest) = Self::unpack_u64(rest)?;
                let (borrow_fee_wad, rest) = Self::unpack_u64(rest)?;
                let (flash_loan_fee_wad, rest) = Self::unpack_u64(rest)?;
                let (host_fee_percentage, rest) = Self::unpack_u8(rest)?;
                let (deposit_limit, rest) = Self::unpack_u64(rest)?;
                let (borrow_limit, rest) = Self::unpack_u64(rest)?;
                let (fee_receiver, rest) = Self::unpack_pubkey(rest)?;
                let (protocol_liquidation_fee, rest) = Self::unpack_u8(rest)?;
                let (protocol_take_rate, rest) = Self::unpack_u8(rest)?;
                let (added_borrow_weight_bps, rest) = Self::unpack_u64(rest)?;
                let (asset_type, rest) = Self::unpack_u8(rest)?;
                let (max_liquidation_bonus, rest) = Self::unpack_u8(rest)?;
                let (max_liquidation_threshold, rest) = Self::unpack_u8(rest)?;
                let (window_duration, rest) = Self::unpack_u64(rest)?;
                let (max_outflow, _rest) = Self::unpack_u64(rest)?;

                Self::UpdateReserveConfig {
                    config: ReserveConfig {
                        optimal_utilization_rate,
                        max_utilization_rate,
                        loan_to_value_ratio,
                        liquidation_bonus,
                        max_liquidation_bonus,
                        liquidation_threshold,
                        max_liquidation_threshold,
                        min_borrow_rate,
                        optimal_borrow_rate,
                        max_borrow_rate,
                        super_max_borrow_rate,
                        fees: ReserveFees {
                            borrow_fee_wad,
                            flash_loan_fee_wad,
                            host_fee_percentage,
                        },
                        deposit_limit,
                        borrow_limit,
                        fee_receiver,
                        protocol_liquidation_fee,
                        protocol_take_rate,
                        added_borrow_weight_bps,
                        reserve_type: ReserveType::from_u8(asset_type).unwrap(),
                    },
                    rate_limiter_config: RateLimiterConfig {
                        window_duration,
                        max_outflow,
                    },
                }
            }
            7 => Self::RedeemFees,
            8 => Self::UpdateMarketMetadata,
            _ => {
                msg!("Instruction cannot be unpacked");
                return Err(LendingError::InstructionUnpackError.into());
            }
        })
    }

    fn unpack_u64(input: &[u8]) -> Result<(u64, &[u8]), ProgramError> {
        if input.len() < 8 {
            msg!("u64 cannot be unpacked");
            return Err(LendingError::InstructionUnpackError.into());
        }
        let (bytes, rest) = input.split_at(8);
        let value = bytes
            .get(..8)
            .and_then(|slice| slice.try_into().ok())
            .map(u64::from_le_bytes)
            .ok_or(LendingError::InstructionUnpackError)?;
        Ok((value, rest))
    }

    fn unpack_u8(input: &[u8]) -> Result<(u8, &[u8]), ProgramError> {
        if input.is_empty() {
            msg!("u8 cannot be unpacked");
            return Err(LendingError::InstructionUnpackError.into());
        }
        let (bytes, rest) = input.split_at(1);
        let value = bytes
            .get(..1)
            .and_then(|slice| slice.try_into().ok())
            .map(u8::from_le_bytes)
            .ok_or(LendingError::InstructionUnpackError)?;
        Ok((value, rest))
    }

    fn unpack_bytes32(input: &[u8]) -> Result<(&[u8; 32], &[u8]), ProgramError> {
        if input.len() < 32 {
            msg!("32 bytes cannot be unpacked");
            return Err(LendingError::InstructionUnpackError.into());
        }
        let (bytes, rest) = input.split_at(32);
        Ok((
            bytes
                .try_into()
                .map_err(|_| LendingError::InstructionUnpackError)?,
            rest,
        ))
    }

    fn unpack_pubkey(input: &[u8]) -> Result<(Pubkey, &[u8]), ProgramError> {
        if input.len() < PUBKEY_BYTES {
            msg!("Pubkey cannot be unpacked");
            return Err(LendingError::InstructionUnpackError.into());
        }
        let (key, rest) = input.split_at(PUBKEY_BYTES);
		let mut buf: [u8;PUBKEY_BYTES] = [0u8; PUBKEY_BYTES];
		buf.copy_from_slice(key);
        let pk = Pubkey::new_from_array(buf);
        Ok((pk, rest))
    }

    /// Packs a [LendingInstruction](enum.LendingInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(size_of::<Self>());
        match *self {
            Self::InitLendingMarket {
                owner,
                quote_currency,
            } => {
                buf.push(0);
                buf.extend_from_slice(owner.as_ref());
                buf.extend_from_slice(quote_currency.as_ref());
            }
            Self::SetLendingMarketOwnerAndConfig {
                new_owner,
                rate_limiter_config: config,
                whitelisted_liquidator,
                risk_authority,
            } => {
                buf.push(1);
                buf.extend_from_slice(new_owner.as_ref());
                buf.extend_from_slice(&config.window_duration.to_le_bytes());
                buf.extend_from_slice(&config.max_outflow.to_le_bytes());
                match whitelisted_liquidator {
                    Some(liquidator) => {
                        buf.push(1);
                        buf.extend_from_slice(liquidator.as_ref());
                    }
                    None => {
                        buf.push(0);
                    }
                };
                buf.extend_from_slice(risk_authority.as_ref());
            }
            Self::InitReserve {
                liquidity_amount,
                config:
                    ReserveConfig {
                        optimal_utilization_rate,
                        max_utilization_rate,
                        loan_to_value_ratio,
                        liquidation_bonus,
                        max_liquidation_bonus,
                        liquidation_threshold,
                        max_liquidation_threshold,
                        min_borrow_rate,
                        optimal_borrow_rate,
                        max_borrow_rate,
                        super_max_borrow_rate,
                        fees:
                            ReserveFees {
                                borrow_fee_wad,
                                flash_loan_fee_wad,
                                host_fee_percentage,
                            },
                        deposit_limit,
                        borrow_limit,
                        fee_receiver,
                        protocol_liquidation_fee,
                        protocol_take_rate,
                        added_borrow_weight_bps: borrow_weight_bps,
                        reserve_type: asset_type,
                    },
            } => {
                buf.push(2);
                buf.extend_from_slice(&liquidity_amount.to_le_bytes());
                buf.extend_from_slice(&optimal_utilization_rate.to_le_bytes());
                buf.extend_from_slice(&max_utilization_rate.to_le_bytes());
                buf.extend_from_slice(&loan_to_value_ratio.to_le_bytes());
                buf.extend_from_slice(&liquidation_bonus.to_le_bytes());
                buf.extend_from_slice(&liquidation_threshold.to_le_bytes());
                buf.extend_from_slice(&min_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&optimal_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&max_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&super_max_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&borrow_fee_wad.to_le_bytes());
                buf.extend_from_slice(&flash_loan_fee_wad.to_le_bytes());
                buf.extend_from_slice(&host_fee_percentage.to_le_bytes());
                buf.extend_from_slice(&deposit_limit.to_le_bytes());
                buf.extend_from_slice(&borrow_limit.to_le_bytes());
                buf.extend_from_slice(&fee_receiver.to_bytes());
                buf.extend_from_slice(&protocol_liquidation_fee.to_le_bytes());
                buf.extend_from_slice(&protocol_take_rate.to_le_bytes());
                buf.extend_from_slice(&borrow_weight_bps.to_le_bytes());
                buf.extend_from_slice(&(asset_type as u8).to_le_bytes());
                buf.extend_from_slice(&max_liquidation_bonus.to_le_bytes());
                buf.extend_from_slice(&max_liquidation_threshold.to_le_bytes());
            }
            Self::RefreshReserve => {
                buf.push(3);
            }
            Self::DepositReserveLiquidity { liquidity_amount } => {
                buf.push(4);
                buf.extend_from_slice(&liquidity_amount.to_le_bytes());
            }
            Self::RedeemReserveCollateral { collateral_amount } => {
                buf.push(5);
                buf.extend_from_slice(&collateral_amount.to_le_bytes());
            }
            Self::UpdateReserveConfig {
                config,
                rate_limiter_config,
            } => {
                buf.push(6);
                buf.extend_from_slice(&config.optimal_utilization_rate.to_le_bytes());
                buf.extend_from_slice(&config.max_utilization_rate.to_le_bytes());
                buf.extend_from_slice(&config.loan_to_value_ratio.to_le_bytes());
                buf.extend_from_slice(&config.liquidation_bonus.to_le_bytes());
                buf.extend_from_slice(&config.liquidation_threshold.to_le_bytes());
                buf.extend_from_slice(&config.min_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&config.optimal_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&config.max_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&config.super_max_borrow_rate.to_le_bytes());
                buf.extend_from_slice(&config.fees.borrow_fee_wad.to_le_bytes());
                buf.extend_from_slice(&config.fees.flash_loan_fee_wad.to_le_bytes());
                buf.extend_from_slice(&config.fees.host_fee_percentage.to_le_bytes());
                buf.extend_from_slice(&config.deposit_limit.to_le_bytes());
                buf.extend_from_slice(&config.borrow_limit.to_le_bytes());
                buf.extend_from_slice(&config.fee_receiver.to_bytes());
                buf.extend_from_slice(&config.protocol_liquidation_fee.to_le_bytes());
                buf.extend_from_slice(&config.protocol_take_rate.to_le_bytes());
                buf.extend_from_slice(&config.added_borrow_weight_bps.to_le_bytes());
                buf.extend_from_slice(&(config.reserve_type as u8).to_le_bytes());
                buf.extend_from_slice(&config.max_liquidation_bonus.to_le_bytes());
                buf.extend_from_slice(&config.max_liquidation_threshold.to_le_bytes());
                buf.extend_from_slice(&rate_limiter_config.window_duration.to_le_bytes());
                buf.extend_from_slice(&rate_limiter_config.max_outflow.to_le_bytes());
            }
            Self::RedeemFees {} => {
                buf.push(7);
            }
            // special handling for this instruction, bc the instruction is too big to deserialize
            Self::UpdateMarketMetadata => {}
        }
        buf
    }
}

/// Creates an 'InitLendingMarket' instruction.
pub fn init_lending_market(
    program_id: Pubkey,
    owner: Pubkey,
    quote_currency: [u8; 32],
    lending_market_pubkey: Pubkey,
    oracle_program_id: Pubkey,
) -> Instruction {
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(lending_market_pubkey, false),
            AccountMeta::new_readonly(sysvar::rent::id(), false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(oracle_program_id, false),
        ],
        data: LendingInstruction::InitLendingMarket {
            owner,
            quote_currency,
        }
        .pack(),
    }
}

/// Creates a 'SetLendingMarketOwner' instruction.
pub fn set_lending_market_owner_and_config(
    program_id: Pubkey,
    lending_market_pubkey: Pubkey,
    lending_market_owner: Pubkey,
    new_owner: Pubkey,
    rate_limiter_config: RateLimiterConfig,
    whitelisted_liquidator: Option<Pubkey>,
    risk_authority: Pubkey,
) -> Instruction {
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(lending_market_pubkey, false),
            AccountMeta::new_readonly(lending_market_owner, true),
        ],
        data: LendingInstruction::SetLendingMarketOwnerAndConfig {
            new_owner,
            rate_limiter_config,
            whitelisted_liquidator,
            risk_authority,
        }
        .pack(),
    }
}

/// Creates an 'InitReserve' instruction.
#[allow(clippy::too_many_arguments)]
pub fn init_reserve(
    program_id: Pubkey,
    liquidity_amount: u64,
    config: ReserveConfig,
    source_liquidity_pubkey: Pubkey,
    destination_collateral_pubkey: Pubkey,
    reserve_pubkey: Pubkey,
    reserve_liquidity_mint_pubkey: Pubkey,
    reserve_liquidity_supply_pubkey: Pubkey,
    reserve_collateral_mint_pubkey: Pubkey,
    reserve_collateral_supply_pubkey: Pubkey,
    pyth_product_pubkey: Pubkey,
    pyth_price_pubkey: Pubkey,
    lending_market_pubkey: Pubkey,
    lending_market_owner_pubkey: Pubkey,
    user_transfer_authority_pubkey: Pubkey,
) -> Instruction {
    let (lending_market_authority_pubkey, _bump_seed) = Pubkey::find_program_address(
        &[&lending_market_pubkey.to_bytes()[..PUBKEY_BYTES]],
        &program_id,
    );
    let accounts = vec![
        AccountMeta::new(source_liquidity_pubkey, false),
        AccountMeta::new(destination_collateral_pubkey, false),
        AccountMeta::new(reserve_pubkey, false),
        AccountMeta::new_readonly(reserve_liquidity_mint_pubkey, false),
        AccountMeta::new(reserve_liquidity_supply_pubkey, false),
        AccountMeta::new(config.fee_receiver, false),
        AccountMeta::new(reserve_collateral_mint_pubkey, false),
        AccountMeta::new(reserve_collateral_supply_pubkey, false),
        AccountMeta::new_readonly(pyth_product_pubkey, false),
        AccountMeta::new_readonly(pyth_price_pubkey, false),
        AccountMeta::new_readonly(lending_market_pubkey, false),
        AccountMeta::new_readonly(lending_market_authority_pubkey, false),
        AccountMeta::new_readonly(lending_market_owner_pubkey, true),
        AccountMeta::new_readonly(user_transfer_authority_pubkey, true),
        AccountMeta::new_readonly(sysvar::rent::id(), false),
        AccountMeta::new_readonly(spl_token::id(), false),
    ];
    Instruction {
        program_id,
        accounts,
        data: LendingInstruction::InitReserve {
            liquidity_amount,
            config,
        }
        .pack(),
    }
}

/// Creates a `RefreshReserve` instruction
pub fn refresh_reserve(
    program_id: Pubkey,
    reserve_pubkey: Pubkey,
    reserve_liquidity_pyth_oracle_pubkey: Pubkey,
) -> Instruction {
    let accounts = vec![
        AccountMeta::new(reserve_pubkey, false),
        AccountMeta::new_readonly(reserve_liquidity_pyth_oracle_pubkey, false),
    ];
    Instruction {
        program_id,
        accounts,
        data: LendingInstruction::RefreshReserve.pack(),
    }
}

/// Creates a 'DepositReserveLiquidity' instruction.
#[allow(clippy::too_many_arguments)]
pub fn deposit_reserve_liquidity(
    program_id: Pubkey,
    liquidity_amount: u64,
    source_liquidity_pubkey: Pubkey,
    destination_collateral_pubkey: Pubkey,
    reserve_pubkey: Pubkey,
    reserve_liquidity_supply_pubkey: Pubkey,
    reserve_collateral_mint_pubkey: Pubkey,
    lending_market_pubkey: Pubkey,
    user_transfer_authority_pubkey: Pubkey,
) -> Instruction {
    let (lending_market_authority_pubkey, _bump_seed) = Pubkey::find_program_address(
        &[&lending_market_pubkey.to_bytes()[..PUBKEY_BYTES]],
        &program_id,
    );
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_liquidity_pubkey, false),
            AccountMeta::new(destination_collateral_pubkey, false),
            AccountMeta::new(reserve_pubkey, false),
            AccountMeta::new(reserve_liquidity_supply_pubkey, false),
            AccountMeta::new(reserve_collateral_mint_pubkey, false),
            AccountMeta::new_readonly(lending_market_pubkey, false),
            AccountMeta::new_readonly(lending_market_authority_pubkey, false),
            AccountMeta::new_readonly(user_transfer_authority_pubkey, true),
            AccountMeta::new_readonly(spl_token::id(), false),
        ],
        data: LendingInstruction::DepositReserveLiquidity { liquidity_amount }.pack(),
    }
}

/// Creates a 'RedeemReserveCollateral' instruction.
#[allow(clippy::too_many_arguments)]
pub fn redeem_reserve_collateral(
    program_id: Pubkey,
    collateral_amount: u64,
    source_collateral_pubkey: Pubkey,
    destination_liquidity_pubkey: Pubkey,
    reserve_pubkey: Pubkey,
    reserve_collateral_mint_pubkey: Pubkey,
    reserve_liquidity_supply_pubkey: Pubkey,
    lending_market_pubkey: Pubkey,
    user_transfer_authority_pubkey: Pubkey,
) -> Instruction {
    let (lending_market_authority_pubkey, _bump_seed) = Pubkey::find_program_address(
        &[&lending_market_pubkey.to_bytes()[..PUBKEY_BYTES]],
        &program_id,
    );
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_collateral_pubkey, false),
            AccountMeta::new(destination_liquidity_pubkey, false),
            AccountMeta::new(reserve_pubkey, false),
            AccountMeta::new(reserve_collateral_mint_pubkey, false),
            AccountMeta::new(reserve_liquidity_supply_pubkey, false),
            AccountMeta::new(lending_market_pubkey, false),
            AccountMeta::new_readonly(lending_market_authority_pubkey, false),
            AccountMeta::new_readonly(user_transfer_authority_pubkey, true),
            AccountMeta::new_readonly(spl_token::id(), false),
        ],
        data: LendingInstruction::RedeemReserveCollateral { collateral_amount }.pack(),
    }
}

/// Creates an 'UpdateReserveConfig' instruction.
#[allow(clippy::too_many_arguments)]
pub fn update_reserve_config(
    program_id: Pubkey,
    config: ReserveConfig,
    rate_limiter_config: RateLimiterConfig,
    reserve_pubkey: Pubkey,
    lending_market_pubkey: Pubkey,
    lending_market_owner_pubkey: Pubkey,
    pyth_product_pubkey: Pubkey,
    pyth_price_pubkey: Pubkey,
) -> Instruction {
    let (lending_market_authority_pubkey, _bump_seed) = Pubkey::find_program_address(
        &[&lending_market_pubkey.to_bytes()[..PUBKEY_BYTES]],
        &program_id,
    );
    let accounts = vec![
        AccountMeta::new(reserve_pubkey, false),
        AccountMeta::new_readonly(lending_market_pubkey, false),
        AccountMeta::new_readonly(lending_market_authority_pubkey, false),
        AccountMeta::new_readonly(lending_market_owner_pubkey, true),
        AccountMeta::new_readonly(pyth_product_pubkey, false),
        AccountMeta::new_readonly(pyth_price_pubkey, false),
    ];
    Instruction {
        program_id,
        accounts,
        data: LendingInstruction::UpdateReserveConfig {
            config,
            rate_limiter_config,
        }
        .pack(),
    }
}

/// Creates a `RedeemFees` instruction
pub fn redeem_fees(
    program_id: Pubkey,
    reserve_pubkey: Pubkey,
    reserve_liquidity_fee_receiver_pubkey: Pubkey,
    reserve_supply_liquidity_pubkey: Pubkey,
    lending_market_pubkey: Pubkey,
) -> Instruction {
    let (lending_market_authority_pubkey, _bump_seed) = Pubkey::find_program_address(
        &[&lending_market_pubkey.to_bytes()[..PUBKEY_BYTES]],
        &program_id,
    );
    let accounts = vec![
        AccountMeta::new(reserve_pubkey, false),
        AccountMeta::new(reserve_liquidity_fee_receiver_pubkey, false),
        AccountMeta::new(reserve_supply_liquidity_pubkey, false),
        AccountMeta::new_readonly(lending_market_pubkey, false),
        AccountMeta::new_readonly(lending_market_authority_pubkey, false),
        AccountMeta::new_readonly(spl_token::id(), false),
    ];
    Instruction {
        program_id,
        accounts,
        data: LendingInstruction::RedeemFees.pack(),
    }
}

/// Creates a `UpdateMarketMetadata` instruction
pub fn update_market_metadata(
    program_id: Pubkey,
    mut metadata: LendingMarketMetadata,
    lending_market_pubkey: Pubkey,
    lending_market_owner: Pubkey,
) -> Instruction {
    let (lending_market_metadata_pubkey, bump_seed) = Pubkey::find_program_address(
        &[
            &lending_market_pubkey.to_bytes()[..PUBKEY_BYTES],
            b"MetaData",
        ],
        &program_id,
    );

    metadata.bump_seed = bump_seed;

    let mut data = [0u8; 1 + std::mem::size_of::<LendingMarketMetadata>()];
    data[0] = 22;
    data[1..].copy_from_slice(bytes_of(&metadata));

    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(lending_market_pubkey, false),
            AccountMeta::new(lending_market_owner, true),
            AccountMeta::new(lending_market_metadata_pubkey, false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: data.to_vec(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::Rng;

    #[test]
    fn pack_and_unpack_instructions() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            {
                let instruction = LendingInstruction::InitLendingMarket {
                    owner: Pubkey::new_unique(),
                    quote_currency: [rng.gen::<u8>(); 32],
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // set lending market owner and config
            {
                let instruction = LendingInstruction::SetLendingMarketOwnerAndConfig {
                    new_owner: Pubkey::new_unique(),
                    rate_limiter_config: RateLimiterConfig {
                        window_duration: rng.gen::<u64>(),
                        max_outflow: rng.gen::<u64>(),
                    },
                    whitelisted_liquidator: if rng.gen_bool(0.5) {
                        None
                    } else {
                        Some(Pubkey::new_unique())
                    },
                    risk_authority: Pubkey::new_unique(),
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            {
                let instruction = LendingInstruction::InitReserve {
                    liquidity_amount: rng.gen::<u64>(),
                    config: ReserveConfig {
                        optimal_utilization_rate: rng.gen::<u8>(),
                        max_utilization_rate: rng.gen::<u8>(),
                        loan_to_value_ratio: rng.gen::<u8>(),
                        liquidation_bonus: rng.gen::<u8>(),
                        max_liquidation_bonus: rng.gen::<u8>(),
                        liquidation_threshold: rng.gen::<u8>(),
                        max_liquidation_threshold: rng.gen::<u8>(),
                        min_borrow_rate: rng.gen::<u8>(),
                        optimal_borrow_rate: rng.gen::<u8>(),
                        max_borrow_rate: rng.gen::<u8>(),
                        super_max_borrow_rate: rng.gen::<u64>(),
                        fees: ReserveFees {
                            borrow_fee_wad: rng.gen::<u64>(),
                            flash_loan_fee_wad: rng.gen::<u64>(),
                            host_fee_percentage: rng.gen::<u8>(),
                        },
                        deposit_limit: rng.gen::<u64>(),
                        borrow_limit: rng.gen::<u64>(),
                        fee_receiver: Pubkey::new_unique(),
                        protocol_liquidation_fee: rng.gen::<u8>(),
                        protocol_take_rate: rng.gen::<u8>(),
                        added_borrow_weight_bps: rng.gen::<u64>(),
                        reserve_type: ReserveType::from_u8(rng.gen::<u8>() % 2).unwrap(),
                    },
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // refresh reserve
            {
                let instruction = LendingInstruction::RefreshReserve;
                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // deposit reserve liquidity
            {
                let instruction = LendingInstruction::DepositReserveLiquidity {
                    liquidity_amount: rng.gen::<u64>(),
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // redeem reserve collateral
            {
                let instruction = LendingInstruction::RedeemReserveCollateral {
                    collateral_amount: rng.gen::<u64>(),
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // update reserve config
            {
                let instruction = LendingInstruction::UpdateReserveConfig {
                    config: ReserveConfig {
                        optimal_utilization_rate: rng.gen::<u8>(),
                        max_utilization_rate: rng.gen::<u8>(),
                        loan_to_value_ratio: rng.gen::<u8>(),
                        liquidation_bonus: rng.gen::<u8>(),
                        max_liquidation_bonus: rng.gen::<u8>(),
                        liquidation_threshold: rng.gen::<u8>(),
                        max_liquidation_threshold: rng.gen::<u8>(),
                        min_borrow_rate: rng.gen::<u8>(),
                        optimal_borrow_rate: rng.gen::<u8>(),
                        max_borrow_rate: rng.gen::<u8>(),
                        super_max_borrow_rate: rng.gen::<u64>(),
                        fees: ReserveFees {
                            borrow_fee_wad: rng.gen::<u64>(),
                            flash_loan_fee_wad: rng.gen::<u64>(),
                            host_fee_percentage: rng.gen::<u8>(),
                        },
                        deposit_limit: rng.gen::<u64>(),
                        borrow_limit: rng.gen::<u64>(),
                        fee_receiver: Pubkey::new_unique(),
                        protocol_liquidation_fee: rng.gen::<u8>(),
                        protocol_take_rate: rng.gen::<u8>(),
                        added_borrow_weight_bps: rng.gen::<u64>(),
                        reserve_type: ReserveType::from_u8(rng.gen::<u8>() % 2).unwrap(),
                    },
                    rate_limiter_config: RateLimiterConfig {
                        window_duration: rng.gen::<u64>(),
                        max_outflow: rng.gen::<u64>(),
                    },
                };

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }

            // redeem fees
            {
                let instruction = LendingInstruction::RedeemFees;

                let packed = instruction.pack();
                let unpacked = LendingInstruction::unpack(&packed).unwrap();
                assert_eq!(instruction, unpacked);
            }
        }
    }
}
