# vm-allocator

`vm-allocator` is a crate designed to to provide allocation and release strategies
that are needed by the VMM during the lifetime of a virtual machine. Possible
resource types that a VMM could allocate using vm-allocator are MMIO addresses,
PIO addresses, GSI numbers, device ids.

We have decided to have two allocator implementations, one for resources that can
be abstracted to an integer and another allocator for addresses. We chose
to have a separate allocator for addresses to add more semantic meaning to this
resources (i.e. it needs informations like alignment which for resources like
interrupt numbers are not needed). The main components are:

- `IDAllocator` - which should be used for all resources that can be reduced to
an integer type.
- `AddressAllocator` - which should be used to allocate address ranges in different
address spaces. This component is a wrapper over `IntervalTree` that adds semantics
to address ranges.

## ID Allocator

### Design

This allocator should be used to allocate resources that can be reduced to an integer
type like legacy GSI numbers or KVM memory slot IDs. The
characteristics of such a resource are represented by the `IdAllocator` struct.

The struct that defines the IdAllocator contains the ends of the interval that is
managed, a field that points at the next available ID and a BTreeSet that is used
to store the released IDs. We choosed to use a BTreeSet because the average
complexity for deletion and insertion is O(logN) compared to Vec for example,
another benefit is that the entries are sorted so we will always use the first
available ID.

#### Allocation policy

When allocating a new ID we always try to return the smallest one available. To
do that we first search in the BTreeSet for any ID that was released and if we
cannot find anything there we return the next ID from the range that was never
allocated.

```rust
/// Id allocator representation.
pub struct IdAllocator {
    // Begining of the range of IDs that we want to manage.
    range_base: u32,
    // First available id that was never allocated. 
    next_id: Option<u32>,
    // End of the range of IDs that we want to manage.
    range_end: u32,
    // Set of all freed ids that can be reused at subsequent allocations.
    freed_ids: BTreeSet<u32>,
}
```

The `IdAllocator` struct implements methods for allocating and releasing IDs.

```rust
impl IdAllocator {
    /// Creates a new instance of IdAllocator that will be used to manage the
    /// allocation and release of ids from the interval specified by
    /// `range_base` and `range_max`
    pub fn new(range_base: u32, range_end: u32) -> std::result::Result<Self, Error> { }

    /// Allocate an ID from the managed ranged.
    pub fn allocate_id(&mut self) -> Result { }

    /// Frees an id from the managed range.
    pub fn free_id(&mut self, id: u32) -> Result { }
}
```

## AddressAllocator

### Design address allocator

This allocator should be used to allocate memory slots, either for memmory-mapped
I/O or for port I/O or any other kind of address space.

The struct that defined the AddressAllocator contains the ends of the interval
that is managed and an instance of `interval_tree` as an allocation engine. We
chose to use `interval_tree` for memory slots allocation because it provides
better creation performance and more query speed.

```rust
/// Address allocator representation
pub struct AddressAllocator {
    // Begining of the address space that we want to manage.
    base: u64,
    // End of the address space that we want to manage.
    end: u64,
    // Allocation engine, the allocation logic that is interfaced
    // by AddressAllocator
    interval_tree: IntervalTree,
}
````

The `AddressAllocator` struct implements methods for allocating and releasing
memory slots from the managed address space.

```rust
impl AddressAllocator {
    ///  Creates a new AddressAllocator object with an empty IntervalTree
    pub fn new(base: u64, size: u64) -> std::result::Result<Self, Error> { }

    /// Allocate a resource range according the allocation constraints.
    pub fn allocate(
        &mut self,
        _address: Option<u64>,
        size: u64,
        align_size: Option<u64>,
        alloc_policy: AllocPolicy,
    ) -> Result<Range> { }

    /// Free an allocated range.
    pub fn free(&mut self, key: &Range) -> Result<()> { }
```

Struct Constraint is used to describe the overall information of the resource needed to be allocated.

```rust
/// Struct to describe resource allocation constraints.
pub struct Constraint {
    /// Size to allocate.
    pub size: u64,
    /// Lower boundary for the allocated resource.
    pub min: u64,
    /// Upper boundary for the allocated resource.
    pub max: u64,
    /// Alignment for the allocated resource.
    pub align: u64,
    /// Resource allocation policy.
    pub policy: AllocPolicy,
}

impl Constraint {
    /// Create a new constraint object with default settings.
    pub fn new(size: u64) -> Self { }

    /// Set the min constraint.
    pub fn min(mut self, min: u64) -> Self { }

    /// Set the max constraint.
    pub fn max(mut self, max: u64) -> Self { }

    /// Set the alignment constraint.
    pub fn align(mut self, align: u64) -> Self { }

    /// Set the allocation policy.
    pub fn policy(mut self, policy: AllocPolicy) -> Self { }
```

### Usage

Add vm-allocator as a dependency in Cargo.toml

```toml
[dependencies]
vm-allocator = "*"
````

Then add extern crate vm-allocator; to projects crate root.
The VMM using this crate should instantiate an IdAllocator object for each resource
type they want to manage.

## License

This project is licensed under either of

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
