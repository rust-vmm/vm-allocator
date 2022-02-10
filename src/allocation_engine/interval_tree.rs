// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2

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

/// A closed interval range [min, max] used to describe a
/// memory slot that will be assigned to a device by the VMM.
/// This structure represents the key of the Node object in
/// the interval tree implementation.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Ord)]
pub struct Range {
    pub min: u64,
    pub max: u64,
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
