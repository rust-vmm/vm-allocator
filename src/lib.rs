// Copyright (C) 2019 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Generic algorithms for VMM resource management.

#![deny(missing_docs)]

mod interval_tree;
pub use interval_tree::{IntervalTree, NodeState, Range};
