// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manages system resources that can be allocated to VMs and their devices.

#![deny(missing_docs)]

/// Allocation engine used by address allocator.
pub mod allocation_engine;
mod id_allocator;

pub use crate::id_allocator::IdAllocator;
use std::result;
use thiserror::Error;

/// Error type for IdAllocator usage.
#[derive(Debug, PartialEq, Error)]
pub enum Error {
    /// Management operations on desired resource resulted in overflow.
    #[error("Management operations on desired resource resulted in overflow.")]
    Overflow,
    /// An id that is not part of the specified range was requested to be released.
    #[error("Specified id: {0} is not in the range.")]
    OutOfRange(u32),
    /// An id that was already released was requested to be released.
    #[error("Specified id: {0} is already released.")]
    AlreadyReleased(u32),
    /// An id  that was never allocated was requested to be released.
    #[error("Specified id: {0} was never allocated, can't release it.")]
    NeverAllocated(u32),
    /// There are no more IDs available in the manage range
    #[error("The requested resource is not available.")]
    ResourceExhausted,
    /// The range to manage is invalid.
    #[error("The range specified: {0}-{1} is not valid.")]
    InvalidRange(u64, u64),
    /// Alignment value is invalid
    #[error("Alignment value is invalid.")]
    InvalidAlignment,
    /// The range that we try to insert into the interval tree is overlapping
    /// with another node from the tree.
    #[error("Addresses are overlapping.{0:?} intersects with existing {1:?}")]
    Overlap(allocation_engine::Range, allocation_engine::Range),
}

/// Wrapper over std::result::Result
pub type Result<T> = result::Result<T, Error>;
