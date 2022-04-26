// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manages system resources that can be allocated to VMs and their devices.

#![deny(missing_docs)]

mod address_allocator;
/// Allocation engine used by address allocator.
mod allocation_engine;
mod id_allocator;

pub use crate::address_allocator::AddressAllocator;
use crate::allocation_engine::NodeState;
pub use crate::id_allocator::IdAllocator;
use std::cmp::max;
use std::cmp::min;
use std::result;
use thiserror::Error;

/// Error type for IdAllocator usage.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Error)]
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
    /// The resource we want to use or update is not available.
    #[error("The requested resource is not available.")]
    ResourceNotAvailable,
    /// The range to manage is invalid.
    #[error("The range specified: {0}-{1} is not valid.")]
    InvalidRange(u64, u64),
    /// Alignment value is invalid
    #[error("Alignment value is invalid.")]
    InvalidAlignment,
    /// The range that we try to insert into the interval tree is overlapping
    /// with another node from the tree.
    #[error("Addresses are overlapping.{0:?} intersects with existing {1:?}")]
    Overlap(RangeInclusive, RangeInclusive),
    /// A node state can be changed just from Free to Allocated, other transitions
    /// are not valid.
    #[error("Invalid state transition for node {0:?} from {1:?} to NodeState::Free")]
    InvalidStateTransition(RangeInclusive, NodeState),
    /// Address is unaligned
    #[error("The address is not aligned.")]
    UnalignedAddress,
    /// Management operations on desired resource resulted in underflow.
    #[error("Management operations on desired resource resulted in underflow.")]
    Underflow,
    /// The size of the desired resource is not invalid.
    #[error("The specified size: {0} is not valid.")]
    InvalidSize(u64),
}

/// Wrapper over std::result::Result
pub type Result<T> = result::Result<T, Error>;

/// A closed interval range [start, end] used to describe a memory slot that
/// will be assigned to a device by the VMM. This structure represents the key
/// of the Node object in the interval tree implementation.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Ord, Debug)]
pub struct RangeInclusive {
    /// Lower boundary of the interval.
    start: u64,
    /// Upper boundary of the interval.
    end: u64,
}

#[allow(clippy::len_without_is_empty)]
impl RangeInclusive {
    /// Create a new RangeInclusive object.
    pub fn new(start: u64, end: u64) -> Result<Self> {
        // The length of the interval [0, u64::MAX] is u64::MAX + 1 which does
        // not fit in a u64::MAX, hence we return `Error::InvalidRange` when
        // there is an attempt to use that range.
        if start >= end || (start == 0 && end == u64::MAX) {
            return Err(Error::InvalidRange(start, end));
        }
        Ok(RangeInclusive { start, end })
    }

    /// Get length of the range.
    pub fn len(&self) -> u64 {
        self.end - self.start + 1
    }

    /// Check whether two RangeInclusive objects overlap with each other.
    pub fn overlaps(&self, other: &RangeInclusive) -> bool {
        max(self.start, other.start) <= min(self.end, other.end)
    }

    /// Check whether the key is fully covered.
    pub fn contains(&self, other: &RangeInclusive) -> bool {
        self.start <= other.start && self.end >= other.end
    }

    /// Get the lower boundary of the range.
    pub fn start(&self) -> u64 {
        self.start
    }

    /// Get the upper boundary of the range.
    pub fn end(&self) -> u64 {
        self.end
    }
}

/// Struct to describe resource allocation constraints.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Constraint {
    /// Size to allocate.
    size: u64,
    /// Alignment for the allocated resource.
    align: u64,
    /// Resource allocation policy.
    policy: AllocPolicy,
}

impl Constraint {
    /// Create a new constraint object with default settings.
    pub fn new(size: u64) -> Result<Self> {
        Ok(Constraint {
            size,
            align: 4,
            policy: AllocPolicy::default(),
        })
    }

    /// Set the alignment constraint.
    pub fn set_align(mut self, align: u64) -> Result<Self> {
        if let AllocPolicy::ExactMatch(start_address) = self.policy {
            if start_address % align != 0 {
                return Err(Error::UnalignedAddress);
            }
        }
        self.align = align;
        Ok(self)
    }

    /// Get the alignment constraint
    pub fn align(self) -> u64 {
        self.align
    }

    /// Set the allocation policy.
    pub fn set_policy(mut self, policy: AllocPolicy) -> Result<Self> {
        if let AllocPolicy::ExactMatch(start_address) = policy {
            if start_address % self.align != 0 {
                return Err(Error::UnalignedAddress);
            }
        }
        self.policy = policy;
        Ok(self)
    }

    /// Get the size constraint
    pub fn size(self) -> u64 {
        self.size
    }
}

/// Policy for resource allocation.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum AllocPolicy {
    /// Allocate the first matched entry.
    FirstMatch,
    /// Allocate first matched entry from the end of the range.
    LastMatch,
    /// Allocate a memory slot starting with the specified address
    /// if it is available.
    ExactMatch(u64),
}

impl Default for AllocPolicy {
    fn default() -> Self {
        AllocPolicy::FirstMatch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_range() {
        assert_eq!(
            RangeInclusive::new(2, 1).unwrap_err(),
            Error::InvalidRange(2, 1)
        );
        assert_eq!(
            RangeInclusive::new(1, 1).unwrap_err(),
            Error::InvalidRange(1, 1)
        );
    }

    #[test]
    fn test_range_overlaps() {
        let range_a = RangeInclusive::new(1u64, 4u64).unwrap();
        let range_b = RangeInclusive::new(4u64, 6u64).unwrap();
        let range_c = RangeInclusive::new(2u64, 3u64).unwrap();
        let range_e = RangeInclusive::new(5u64, 6u64).unwrap();

        assert!(range_a.overlaps(&range_b));
        assert!(range_b.overlaps(&range_a));
        assert!(range_a.overlaps(&range_c));
        assert!(range_c.overlaps(&range_a));
        assert!(!range_a.overlaps(&range_e));
        assert!(!range_e.overlaps(&range_a));

        assert_eq!(range_a.len(), 4);
    }

    #[test]
    fn test_range_contain() {
        let range_a = RangeInclusive::new(2u64, 6u64).unwrap();
        assert!(range_a.contains(&RangeInclusive::new(2u64, 3u64).unwrap()));
        assert!(range_a.contains(&RangeInclusive::new(3u64, 4u64).unwrap()));
        assert!(range_a.contains(&RangeInclusive::new(5u64, 6u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(1u64, 2u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(1u64, 3u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(1u64, 7u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(7u64, 8u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(6u64, 7u64).unwrap()));
        assert!(!range_a.contains(&RangeInclusive::new(7u64, 8u64).unwrap()));
    }

    #[test]
    fn test_range_ord() {
        let range_a = RangeInclusive::new(1, 4).unwrap();
        let range_b = RangeInclusive::new(1, 4).unwrap();
        let range_c = RangeInclusive::new(1, 3).unwrap();
        let range_d = RangeInclusive::new(1, 5).unwrap();

        assert_eq!(range_a, range_b);
        assert_eq!(range_b, range_a);
        assert!(range_a > range_c);
        assert!(range_c < range_a);
        assert!(range_a < range_d);
        assert!(range_d > range_a);
    }

    #[test]
    fn test_getters() {
        let range = RangeInclusive::new(3, 5).unwrap();
        assert_eq!(range.start(), 3);
        assert_eq!(range.end(), 5);
    }

    #[test]
    fn test_range_upper_bound() {
        let range = RangeInclusive::new(0, u64::MAX);
        assert_eq!(range.unwrap_err(), Error::InvalidRange(0, u64::MAX));
    }
}
