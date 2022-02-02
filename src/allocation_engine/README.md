# Interval Tree allocation engine

## Design

This interval tree implementation is defined to work as an allocation
engine for memory-mapped I/O and port I/O address space. It provides
underlaying methods for allocating, releaseing and updating a memory
slot. This implementation is going to be used by address allocator
component of vm-allocator, its main goal is to make address slots
allocation easier to track and maintain.

```rust
pub struct IntervalTree {
    pub(crate) root: Option<InnerNode>,
}

/// Internal tree node to implement interval tree.
#[derive(Debug, PartialEq)]
pub(crate) struct InnerNode {
    /// Interval handled by this node.
    pub(crate) key: Range,
    /// Optional contained data, None if the node is free.
    pub(crate) node_state: NodeState,
    /// Optional left child of current node.
    pub(crate) left: Option<Box<InnerNode>>,
    /// Optional right child of current node.
    pub(crate) right: Option<Box<InnerNode>>,
    /// Cached height of the node.
    pub(crate) height: u64,
    /// Cached maximum valued covered by this node.
    pub(crate) max_key: u64,
}

pub enum NodeState {
    /// Node is free
    Free,
    /// Node is allocated but without associated data
    Allocated,
}

/// Insert the ket into the interval tree, returns Error if intersects with existing nodes.
pub fn insert(&mut self, key: Range, node_state: NodeState) -> Result<()> { }

/// Update an existing entry and return the old value.
pub(crate) fn update(&mut self, key: &Range, node_state: NodeState) -> Result<()> { }

/// Remove the `key` from the tree and return the associated data.
pub fn delete(&mut self, key: &Range) -> Option<()> { }

 /// Construct a new empty IntervalTree.
pub fn new() -> Self { }

/// Check whether the interval tree is empty.
pub fn is_empty(&self) -> bool { }

/// Get the data item associated with the key, or return None if no match found.
pub fn get(&self, key: &Range) -> Option<NodeState> { }

/// Get a shared reference to the node fully covering the entire key range.
pub fn get_superset(&self, key: &Range) -> Option<(&Range, NodeState)> { }
```

### Address allocation policy

We offer three options for placing and memory slot in the managed address space:

1. `LastMatch` -> When using this allocation policy the allocator will try to
insert the range described by the constraint at the first available position
starting from the end of the managed address space.
2. `FirstMatch` -> When using this allocation policy the allocator will try to
insert the range described by the constraint at the first available position
starting from the begining of the managed address space.
3. `ExactMatch` -> When using this allocation policy the allocator will try to
insert the range at the exact position described by the constraint, otherwise
it will return an error.

## Usage

The concept of Interval Tree may seem complicated, but using vm-allocator to do
resource allocation and release is simple and straightforward.

```rust
// 1. To start with, we should create an interval tree for some specific resouces 
// and give an address space as a root node

#[derive(Debug, PartialEq)]
pub struct AddressAllocator {
    base: u64,
    end: u64,
    interval_tree: IntervalTree,
}

impl AddressAllocator {
    pub fn new(base: u64, size: u64) -> std::result::Result<Self, Error> {
        let interval_tree = IntervalTree::new();
        let mut address_allocator = AddressAllocator {
            base: base,
            end: end.unwrap(),
            interval_tree: interval_tree,
        };

        address_allocator
            .interval_tree
            .insert(Range::new(base, end.unwrap())?, NodeState::Free)?;
        Ok(address_allocator)
    }


// 2. Next, create a constraint with the size for your resource, you could also assign the maximum, minimum and alignment for the constraint. Then we could use the constraint to allocate the resource in the range we previously decided. Interval Tree will give you the appropriate range. 
 pub fn allocate(
        &mut self,
        _address: Option<u64>,
        size: u64,
        align_size: Option<u64>,
        alloc_policy: AllocPolicy,
    ) -> Result<Range> {
        let constraint = Constraint::new(size).align(alignment).policy(alloc_policy);
        // some other code here
        if logical_condition {
            let key = self.interval_tree.find_candidate(&constaint);
            self.interval_tree.insert(key, NodeState::Allocated);
        }
    }
```

## License

**!!!NOTICE**: The BSD-3-Clause license is not included in this template.
The license needs to be manually added because the text of the license file
also includes the copyright. The copyright can be different for different
crates. If the crate contains code from CrosVM, the crate must add the
CrosVM copyright which can be found
[here](https://chromium.googlesource.com/chromiumos/platform/crosvm/+/master/LICENSE).
For crates developed from scratch, the copyright is different and depends on
the contributors.
