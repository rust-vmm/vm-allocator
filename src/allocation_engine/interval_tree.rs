// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2

use crate::{Error, Result};
use std::cmp::{max, min};

/// Policy for resource allocation.
#[derive(Copy, Clone, Debug, PartialEq)]
#[allow(dead_code)]
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

/// Struct to describe resource allocation constraints.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Constraint {
    /// Size to allocate.
    pub size: u64,
    /// Range where the allocated resource will be placed.
    pub desired_range: Range,
    /// Alignment for the allocated resource.
    pub align: u64,
    /// Resource allocation policy.
    pub policy: AllocPolicy,
}

/// A closed interval range [start, end] used to describe a
/// memory slot that will be assigned to a device by the VMM.
/// This structure represents the key of the Node object in
/// the interval tree implementation.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Ord, Debug)]
pub struct Range {
    /// Lower boundary of the interval.
    start: u64,
    /// Upper boundary of the interval.
    end: u64,
}

#[allow(clippy::len_without_is_empty)]
impl Range {
    /// Create a new Range object.
    pub fn new(start: u64, end: u64) -> Result<Self> {
        if start > end {
            return Err(Error::InvalidRange(start, end));
        }
        Ok(Range { start, end })
    }

    /// Get length of the range.
    pub fn len(&self) -> u64 {
        self.end - self.start + 1
    }

    /// Check whether two Range objects overlap with each other.
    pub fn overlaps(&self, other: &Range) -> bool {
        max(self.start, other.start) <= min(self.end, other.end)
    }

    /// Check whether the key is fully covered.
    pub fn contains(&self, other: &Range) -> bool {
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

/// Returns the first multiple of `alignment` that is lower or equal to the
/// specified address. This method works only for alignment values that are a
/// power of two.
///
/// # Examples
/// ```rust
/// extern crate vm_allocator;
/// use vm_allocator::allocation_engine::{align_down, Range};
/// use vm_allocator::Error;
/// use vm_allocator::Result;
///
/// fn intervals_align_down() -> Result<u64> {
///     let address = 5;
///     if let Ok(res) = align_down(address, 2) {
///         if res == 4 {
///             return Ok(res);
///         }
///         return Err(Error::Overflow);
///     }
///     Err(Error::Overflow)
/// }
///
/// # intervals_align_down().unwrap();
/// ```
pub fn align_down(address: u64, alignment: u64) -> Result<u64> {
    if !alignment.is_power_of_two() {
        return Err(Error::InvalidAlignment);
    }
    Ok(address & !(alignment - 1))
}

/// Returns the first multiple of `alignment` that is greater or equal to the
/// specified address. This method works only for alignment values that are a
/// power of two.
///
/// # Examples
/// ```rust
/// extern crate vm_allocator;
/// use vm_allocator::allocation_engine::{align_up, Range};
/// use vm_allocator::Error;
/// use vm_allocator::Result;
///
/// fn intervals_align_up() -> Result<u64> {
///     let address = 3;
///     if let Ok(res) = align_up(address, 2) {
///         if res == 4 {
///             return Ok(res);
///         }
///         return Err(Error::Overflow);
///     }
///     Err(Error::Overflow)
/// }
///
/// # intervals_align_up().unwrap();
/// ```
pub fn align_up(address: u64, alignment: u64) -> Result<u64> {
    if alignment == 0 {
        return Err(Error::InvalidAlignment);
    }
    if let Some(intermediary_address) = address.checked_add(alignment - 1) {
        return align_down(intermediary_address, alignment);
    }
    Err(Error::Overflow)
}

/// Node state for interval tree nodes.
///
/// Valid state transition:
/// - None -> Free: IntervalTree::insert()
/// - Free -> Allocated: IntervalTree::allocate()
/// - Allocated -> Free: IntervalTree::free()
/// - * -> None: IntervalTree::delete()
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum NodeState {
    /// Node is free.
    Free,
    /// Node is allocated.
    Allocated,
}

/// Internal tree node to implement interval tree.
#[derive(Debug, PartialEq)]
struct InnerNode {
    /// Interval handled by this node.
    key: Range,
    /// NodeState, can be Free or Allocated.
    node_state: NodeState,
    /// Optional left child of current node.
    left: Option<Box<InnerNode>>,
    /// Optional right child of current node.
    right: Option<Box<InnerNode>>,
    /// Cached height of the node.
    height: u64,
    /// Cached maximum valued covered by this node.
    max_key: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_range() {
        assert_eq!(Range::new(2, 1).unwrap_err(), Error::InvalidRange(2, 1));
    }

    #[test]
    fn test_range_overlaps() {
        let range_a = Range::new(1u64, 4u64).unwrap();
        let range_b = Range::new(4u64, 6u64).unwrap();
        let range_c = Range::new(2u64, 3u64).unwrap();
        let range_d = Range::new(4u64, 4u64).unwrap();
        let range_e = Range::new(5u64, 6u64).unwrap();

        assert!(range_a.overlaps(&range_b));
        assert!(range_b.overlaps(&range_a));
        assert!(range_a.overlaps(&range_c));
        assert!(range_c.overlaps(&range_a));
        assert!(range_a.overlaps(&range_d));
        assert!(range_d.overlaps(&range_a));
        assert!(!range_a.overlaps(&range_e));
        assert!(!range_e.overlaps(&range_a));

        assert_eq!(range_a.len(), 4);
        assert_eq!(range_d.len(), 1);
    }

    #[test]
    fn test_range_contain() {
        let range_a = Range::new(2u64, 6u64).unwrap();
        assert!(range_a.contains(&Range::new(2u64, 3u64).unwrap()));
        assert!(range_a.contains(&Range::new(3u64, 4u64).unwrap()));
        assert!(range_a.contains(&Range::new(5u64, 5u64).unwrap()));
        assert!(range_a.contains(&Range::new(5u64, 6u64).unwrap()));
        assert!(range_a.contains(&Range::new(6u64, 6u64).unwrap()));
        assert!(!range_a.contains(&Range::new(1u64, 1u64).unwrap()));
        assert!(!range_a.contains(&Range::new(1u64, 2u64).unwrap()));
        assert!(!range_a.contains(&Range::new(1u64, 3u64).unwrap()));
        assert!(!range_a.contains(&Range::new(1u64, 7u64).unwrap()));
        assert!(!range_a.contains(&Range::new(7u64, 8u64).unwrap()));
        assert!(!range_a.contains(&Range::new(6u64, 7u64).unwrap()));
        assert!(!range_a.contains(&Range::new(7u64, 8u64).unwrap()));
    }

    #[test]
    fn test_range_align_up() {
        assert_eq!(align_up(2, 0).unwrap_err(), Error::InvalidAlignment);
        assert_eq!(align_up(2, 1).unwrap(), 2);
        assert_eq!(align_up(2, 2).unwrap(), 2);
        assert_eq!(align_up(2, 4).unwrap(), 4);
        assert_eq!(align_up(2, 3).unwrap_err(), Error::InvalidAlignment);

        assert_eq!(
            align_up(0xFFFF_FFFF_FFFF_FFFDu64, 2).unwrap(),
            0xFFFF_FFFF_FFFF_FFFEu64
        );
        assert_eq!(
            align_up(0xFFFF_FFFF_FFFF_FFFDu64, 4).unwrap_err(),
            Error::Overflow
        );
    }

    #[test]
    fn test_range_ord() {
        let range_a = Range::new(1u64, 4u64).unwrap();
        let range_b = Range::new(1u64, 4u64).unwrap();
        let range_c = Range::new(1u64, 3u64).unwrap();
        let range_d = Range::new(1u64, 5u64).unwrap();
        let range_e = Range::new(2u64, 2u64).unwrap();

        assert_eq!(range_a, range_b);
        assert_eq!(range_b, range_a);
        assert!(range_a > range_c);
        assert!(range_c < range_a);
        assert!(range_a < range_d);
        assert!(range_d > range_a);
        assert!(range_a < range_e);
        assert!(range_e > range_a);
    }

    #[test]
    fn test_getters() {
        let range = Range::new(3, 5).unwrap();
        assert_eq!(range.start(), 3);
        assert_eq!(range.end(), 5);
    }
}
