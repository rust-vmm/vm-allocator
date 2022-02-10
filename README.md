# vm-allocator

`vm-allocator` is a crate designed to provide allocation and release strategies
that are needed by the VMM during the lifetime of a virtual machine. Possible
resource types that a VMM could allocate using vm-allocator are MMIO addresses,
PIO addresses, GSI numbers, device IDs.

We have decided to have two allocator implementations, one for resources that can
be abstracted to an integer and another allocator for addresses. We chose
to have a separate allocator for addresses to add more semantic meaning to this
resource (i.e. it needs information like alignment which for resources like
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
to store the released IDs. We choose to use a BTreeSet because the average
complexity for deletion and insertion is O(log N) compared to Vec for example,
another benefit is that the entries are sorted so, we will always use the first
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
