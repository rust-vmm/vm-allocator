# vm-allocator

`vm-allocator` is a crate designed to provide allocation and release strategies
that are needed by the VMM during the lifetime of a virtual machine. Possible
resource types that a VMM could allocate using vm-allocator are MMIO addresses,
PIO addresses, GSI numbers, device IDs.

This crate exports 2 allocators: one for resources that can be represented as
integers, and one for addresses. The reason behind having two separate
allocators is the need to add semantic meaning to the address allocator, by
specifying configuration parameters such as the alignment that do not make
sense in the context of IDs.

The main components of the crate are:
- `IDAllocator` - which should be used for all resources that can be reduced to
  an integer type.
- `AddressAllocator` - which should be used to allocate address ranges in
  different address spaces. This component is a wrapper over `IntervalTree`
  that adds semantics to address ranges. More details about the inner
  presentation of the address allocator can be found in the
  [Design Document](src/allocation_engine/DESIGN.md).

## ID Allocator

### Design

This allocator should be used to allocate resources that can be reduced to an
integer type like legacy GSI numbers or KVM memory slot IDs. The
characteristics of such a resource are represented by the `IdAllocator` struct.

The struct that defines the `IdAllocator` contains the end of the interval that
is managed, a field that points at the next available ID and a `BTreeSet` that
is used to store the released IDs. The reason for using a `BTreeSet` is that
the average complexity for deletion and insertion is `O(log N)`, offering a
better performance when compared to Vector for example. The entries are sorted,
so we will always use the first available ID.

#### Allocation policy

When allocating a new ID we always try to return the smallest one available. To
do that we first search in the BTreeSet for any ID that was released and if we
cannot find anything there we return the next ID from the range that was never
allocated.

The `IdAllocator` struct implements methods for allocating and releasing IDs.

### Usage

Add vm-allocator as a dependency in Cargo.toml

```toml
[dependencies]
vm-allocator = "*"
````

Then add extern crate vm-allocator; to projects crate root.
The VMM using this crate should instantiate an IdAllocator object for each
resource type they want to manage.

## License

This project is licensed under either of

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
