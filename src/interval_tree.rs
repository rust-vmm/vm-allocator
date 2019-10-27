// Copyright (C) 2019 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! A special interval tree implementation for VMM resource management.
//!
//! It's not designed as a generic interval tree, but specialized for VMM resource management.
//! In addition to the normal get/insert/delete/update operations, it also implements allocate/free.

use std::cmp::{max, min, Ordering};

/// A closed interval range [min, max].
#[allow(missing_docs)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Hash)]
pub struct Range {
    pub min: u64,
    pub max: u64,
}

impl Range {
    /// Create a new Range object.
    ///
    /// Note: panic if encounters invalid parameters.
    pub fn new<T>(min: T, max: T) -> Self
    where
        u64: From<T>,
    {
        let umin = u64::from(min);
        let umax = u64::from(max);
        if umin > umax || (umin == 0 && umax == std::u64::MAX) {
            panic!("interval_tree: Range({}, {}) is invalid", umin, umax);
        }
        Range {
            min: umin,
            max: umax,
        }
    }

    /// Create a new Range object.
    ///
    /// Note: panic if encounters invalid parameters.
    pub fn with_size<T>(base: T, size: T) -> Self
    where
        u64: From<T>,
    {
        let umin = u64::from(base);
        let umax = u64::from(size).checked_add(umin).unwrap();
        if umin > umax || (umin == 0 && umax == std::u64::MAX) {
            panic!("interval_tree: Range({}, {}) is invalid", umin, umax);
        }
        Range {
            min: umin,
            max: umax,
        }
    }

    /// Create a new Range object containing just a point.
    pub fn new_point<T>(value: T) -> Self
    where
        u64: From<T>,
    {
        let val = u64::from(value);
        Range { min: val, max: val }
    }

    /// Get length of the range.
    pub fn len(&self) -> u64 {
        self.max - self.min + 1
    }

    /// Check whether the range is empty.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Check whether two Range objects intersect with each other.
    pub fn intersect(&self, other: &Range) -> bool {
        max(self.min, other.min) <= min(self.max, other.max)
    }
}

impl Ord for Range {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.min.cmp(&other.min) {
            Ordering::Equal => self.max.cmp(&other.max),
            res => res,
        }
    }
}

/// Node state for interval tree nodes.
///
/// Valid state transition:
/// - None -> Free: IntervalTree::insert()
/// - None -> Valued: IntervalTree::insert()
/// - Free -> Allocated: IntervalTree::allocate()
/// - Allocated -> Valued(T): IntervalTree::update()
/// - Valued -> Valued(T): IntervalTree::update()
/// - Allocated -> Free: IntervalTree::free()
/// - Valued(T) -> Free: IntervalTree::free()
/// - * -> None: IntervalTree::delete()
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum NodeState<T> {
    /// Node is free
    Free,
    /// Node is allocated but without associated data
    Allocated,
    /// Node is allocated with associated data.
    Valued(T),
}

impl<T> NodeState<T> {
    fn take(&mut self) -> Self {
        std::mem::replace(self, NodeState::<T>::Free)
    }

    fn replace(&mut self, value: NodeState<T>) -> Self {
        std::mem::replace(self, value)
    }

    fn as_ref(&self) -> NodeState<&T> {
        match self {
            NodeState::<T>::Valued(ref x) => NodeState::<&T>::Valued(x),
            NodeState::<T>::Allocated => NodeState::<&T>::Allocated,
            NodeState::<T>::Free => NodeState::<&T>::Free,
        }
    }
}

impl<T> Into<Option<T>> for NodeState<T> {
    fn into(self) -> Option<T> {
        match self {
            NodeState::<T>::Free | NodeState::<T>::Allocated => None,
            NodeState::<T>::Valued(data) => Some(data),
        }
    }
}

/// Internal tree node to implement interval tree.
#[derive(Debug)]
struct InnerNode<T> {
    /// Interval handled by this node.
    key: Range,
    /// Optional contained data, None if the node is free.
    data: NodeState<T>,
    /// Optional left child of current node.
    left: Option<Node<T>>,
    /// Optional right child of current node.
    right: Option<Node<T>>,
    /// Cached height of the node.
    height: u32,
    /// Cached maximum valued covered by this node.
    max_key: u64,
}

impl<T> InnerNode<T> {
    fn new(key: Range, data: NodeState<T>) -> Self {
        InnerNode {
            key,
            data,
            left: None,
            right: None,
            height: 1,
            max_key: key.max,
        }
    }
}

/// Newtype for interval tree nodes.
#[derive(Debug)]
struct Node<T>(Box<InnerNode<T>>);

impl<T> Node<T> {
    fn new(key: Range, data: Option<T>) -> Self {
        let value = if let Some(t) = data {
            NodeState::Valued(t)
        } else {
            NodeState::Free
        };
        Node(Box::new(InnerNode::new(key, value)))
    }

    /// Returns a readonly reference to the node associated with the `key` or None if not found.
    fn search(&self, key: &Range) -> Option<&Self> {
        match self.0.key.cmp(key) {
            Ordering::Equal => Some(self),
            Ordering::Less => self.0.right.as_ref().and_then(|node| node.search(key)),
            Ordering::Greater => self.0.left.as_ref().and_then(|node| node.search(key)),
        }
    }

    /// Insert a new (key, data) pair into the subtree.
    ///
    /// Note: it will panic if the new key intersects with existing nodes.
    fn insert(mut self, key: Range, data: Option<T>) -> Self {
        match self.0.key.cmp(&key) {
            Ordering::Equal => {
                panic!("interval_tree: key {:?} exists", key);
            }
            Ordering::Less => {
                if self.0.key.intersect(&key) {
                    panic!(
                        "interval_tree: key {:?} intersects with existing {:?}",
                        key, self.0.key
                    );
                }
                match self.0.right {
                    None => self.0.right = Some(Node::new(key, data)),
                    Some(_) => self.0.right = self.0.right.take().map(|n| n.insert(key, data)),
                }
            }
            Ordering::Greater => {
                if self.0.key.intersect(&key) {
                    panic!(
                        "interval_tree: key {:?} intersects with existing {:?}",
                        key, self.0.key
                    );
                }
                match self.0.left {
                    None => self.0.left = Some(Node::new(key, data)),
                    Some(_) => self.0.left = self.0.left.take().map(|n| n.insert(key, data)),
                }
            }
        }
        self.updated_node()
    }

    /// Delete `key` from the subtree.
    ///
    /// Note: it doesn't return whether the key exists in the subtree, so caller need to ensure the
    /// logic.
    fn delete(mut self, key: &Range) -> (Option<T>, Option<Self>) {
        match self.0.key.cmp(&key) {
            Ordering::Equal => {
                let data = self.0.data.take();
                return (data.into(), self.delete_root());
            }
            Ordering::Less => {
                if let Some(node) = self.0.right.take() {
                    let (data, right) = node.delete(key);
                    self.0.right = right;
                    return (data, Some(self.updated_node()));
                }
            }
            Ordering::Greater => {
                if let Some(node) = self.0.left.take() {
                    let (data, left) = node.delete(key);
                    self.0.left = left;
                    return (data, Some(self.updated_node()));
                }
            }
        }
        (None, Some(self))
    }

    /// Rotate the node if necessary to keep balance.
    fn rotate(self) -> Self {
        let l = height(&self.0.left);
        let r = height(&self.0.right);
        match (l as i32) - (r as i32) {
            1 | 0 | -1 => self,
            2 => self.rotate_left_successor(),
            -2 => self.rotate_right_successor(),
            _ => unreachable!(),
        }
    }

    /// Perform a single left rotation on this node.
    fn rotate_left(mut self) -> Self {
        let mut new_root = self.0.right.take().expect("Node is broken");
        self.0.right = new_root.0.left.take();
        self.update_cached_info();
        new_root.0.left = Some(self);
        new_root.update_cached_info();
        new_root
    }

    /// Perform a single right rotation on this node.
    fn rotate_right(mut self) -> Self {
        let mut new_root = self.0.left.take().expect("Node is broken");
        self.0.left = new_root.0.right.take();
        self.update_cached_info();
        new_root.0.right = Some(self);
        new_root.update_cached_info();
        new_root
    }

    /// Performs a rotation when the left successor is too high.
    fn rotate_left_successor(mut self) -> Self {
        let left = self.0.left.take().expect("Node is broken");
        if height(&left.0.left) < height(&left.0.right) {
            let rotated = left.rotate_left();
            self.0.left = Some(rotated);
            self.update_cached_info();
        } else {
            self.0.left = Some(left);
        }
        self.rotate_right()
    }

    /// Performs a rotation when the right successor is too high.
    fn rotate_right_successor(mut self) -> Self {
        let right = self.0.right.take().expect("Node is broken");
        if height(&right.0.left) > height(&right.0.right) {
            let rotated = right.rotate_right();
            self.0.right = Some(rotated);
            self.update_cached_info();
        } else {
            self.0.right = Some(right);
        }
        self.rotate_left()
    }

    fn delete_root(mut self) -> Option<Self> {
        match (self.0.left.take(), self.0.right.take()) {
            (None, None) => None,
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            (Some(l), Some(r)) => Some(Self::combine_subtrees(l, r)),
        }
    }

    /// Find the minimal key below the tree and returns a new optional tree where the minimal
    /// value has been removed and the (optional) minimal node as tuple (min_node, remaining)
    fn get_new_root(mut self) -> (Self, Option<Self>) {
        match self.0.left.take() {
            None => {
                let remaining = self.0.right.take();
                (self, remaining)
            }
            Some(left) => {
                let (min_node, left) = left.get_new_root();
                self.0.left = left;
                (min_node, Some(self.updated_node()))
            }
        }
    }

    fn combine_subtrees(l: Self, r: Self) -> Self {
        let (mut new_root, remaining) = r.get_new_root();
        new_root.0.left = Some(l);
        new_root.0.right = remaining;
        new_root.updated_node()
    }

    /// Update cached information of the node.
    /// Please make sure that the cached values of both children are up to date.
    fn update_cached_info(&mut self) {
        self.0.height = max(height(&self.0.left), height(&self.0.right)) + 1;
        self.0.max_key = max(
            max_key(&self.0.left),
            max(max_key(&self.0.right), self.0.key.max),
        );
    }

    /// Update the sub-tree to keep balance.
    fn updated_node(mut self) -> Self {
        self.update_cached_info();
        self.rotate()
    }
}

/// Compute height of the optional sub-tree.
fn height<T>(node: &Option<Node<T>>) -> u32 {
    node.as_ref().map_or(0, |n| n.0.height)
}

/// Compute maximum key value covered by the optional sub-tree.
fn max_key<T>(node: &Option<Node<T>>) -> u64 {
    node.as_ref().map_or(0, |n| n.0.max_key)
}

/// A specialized interval tree implementation for VMM resource management.
#[derive(Debug, Default)]
pub struct IntervalTree<T> {
    root: Option<Node<T>>,
}

impl<T> IntervalTree<T> {
    /// Construct a new empty IntervalTree.
    ///
    /// # Examples
    /// ```rust
    /// extern crate vm_allocator;
    ///
    /// let tree = vm_allocator::IntervalTree::<u64>::new();
    /// ```
    pub fn new() -> Self {
        IntervalTree { root: None }
    }

    /// Check whether the interval tree is empty.
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Get the data item associated with the key, or return None if no match found.
    ///
    /// # Examples
    /// ```rust
    /// extern crate vm_allocator;
    /// use vm_allocator::{IntervalTree, Range, NodeState};
    ///
    /// let mut tree = vm_allocator::IntervalTree::<u64>::new();
    /// assert!(tree.is_empty());
    /// assert_eq!(tree.get(&Range::new(0x101u64, 0x101u64)), None);
    /// tree.insert(Range::new(0x100u64, 0x100u64), Some(1));
    /// tree.insert(Range::new(0x200u64, 0x2ffu64), None);
    /// assert!(!tree.is_empty());
    /// assert_eq!(tree.get(&Range::new(0x100u64, 0x100u64)), Some(NodeState::Valued(&1)));
    /// assert_eq!(tree.get(&Range::new(0x200u64, 0x2ffu64)), Some(NodeState::Free));
    /// assert_eq!(tree.get(&Range::new(0x101u64, 0x101u64)), None);
    /// assert_eq!(tree.get(&Range::new(0x100u64, 0x101u64)), None);
    /// ```
    pub fn get(&self, key: &Range) -> Option<NodeState<&T>> {
        match self.root {
            None => None,
            Some(ref node) => node.search(key).map(|n| n.0.data.as_ref()),
        }
    }

    /// Insert the (key, data) pair into the interval tree, panic if intersects with existing nodes.
    ///
    /// # Examples
    /// ```rust
    /// extern crate vm_allocator;
    /// use vm_allocator::{IntervalTree, Range, NodeState};
    ///
    /// let mut tree = IntervalTree::<u64>::new();
    /// tree.insert(Range::new(0x100u32, 0x100u32), Some(1));
    /// tree.insert(Range::new(0x200u32, 0x2ffu32), None);
    /// assert_eq!(tree.get(&Range::new(0x100u64, 0x100u64)), Some(NodeState::Valued(&1)));
    /// assert_eq!(tree.get(&Range::new(0x200u64, 0x2ffu64)), Some(NodeState::Free));
    /// ```
    pub fn insert(&mut self, key: Range, data: Option<T>) {
        match self.root.take() {
            None => self.root = Some(Node::new(key, data)),
            Some(node) => self.root = Some(node.insert(key, data)),
        }
    }

    /// Remove the `key` from the tree and return the associated data.
    ///
    /// # Examples
    /// ```rust
    /// extern crate vm_allocator;
    /// use vm_allocator::{IntervalTree, Range};
    ///
    /// let mut tree = IntervalTree::<u64>::new();
    /// tree.insert(Range::new(0x100u64, 0x100u64), Some(1));
    /// tree.insert(Range::new(0x200u64, 0x2ffu64), None);
    /// let old = tree.delete(&Range::new(0x100u64, 0x100u64));
    /// assert_eq!(old, Some(1));
    /// let old = tree.delete(&Range::new(0x200u64, 0x2ffu64));
    /// assert_eq!(old, None);
    /// ```
    pub fn delete(&mut self, key: &Range) -> Option<T> {
        match self.root.take() {
            Some(node) => {
                let (data, root) = node.delete(key);
                self.root = root;
                data
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn test_new_range() {
        let _ = Range::new(2u8, 1u8);
    }

    #[test]
    #[should_panic]
    fn test_new_range_overflow() {
        let _ = Range::new(0u64, std::u64::MAX);
    }

    #[test]
    fn test_range_intersect() {
        let a = Range::new(1u8, 4u8);
        let b = Range::new(4u16, 6u16);
        let c = Range::new(2u32, 3u32);
        let d = Range::new(4u64, 4u64);
        let e = Range::new(5u32, 6u32);

        assert!(a.intersect(&b));
        assert!(b.intersect(&a));
        assert!(a.intersect(&c));
        assert!(c.intersect(&a));
        assert!(a.intersect(&d));
        assert!(d.intersect(&a));
        assert!(!a.intersect(&e));
        assert!(!e.intersect(&a));

        assert_eq!(a.len(), 4);
        assert_eq!(d.len(), 1);
    }

    #[test]
    fn test_range_ord() {
        let a = Range::new(1u32, 4u32);
        let b = Range::new(1u32, 4u32);
        let c = Range::new(1u32, 3u32);
        let d = Range::new(1u32, 5u32);
        let e = Range::new(2u32, 2u32);

        assert_eq!(a, b);
        assert_eq!(b, a);
        assert!(a > c);
        assert!(c < a);
        assert!(a < d);
        assert!(d > a);
        assert!(a < e);
        assert!(e > a);
    }

    #[should_panic]
    #[test]
    fn test_tree_insert_equal() {
        let mut tree = IntervalTree::<u64>::new();
        tree.insert(Range::new(0x100u16, 0x200), Some(1));
        tree.insert(Range::new(0x100u32, 0x200), None);
    }

    #[should_panic]
    #[test]
    fn test_tree_insert_intersect() {
        let mut tree = IntervalTree::<u64>::new();
        tree.insert(Range::new(0x100, 0x200u32), Some(1));
        tree.insert(Range::new(0x200, 0x2ffu64), None);
    }
}
