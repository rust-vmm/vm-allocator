# Changelog

## Upcoming version

### Added
### Changed
### Fixed
### Removed
### Deprecated

## [v0.1.4]

### Added

- Support for no_std environments.
- [[#120]](https://github.com/rust-vmm/vm-allocator/pull/120): `IdAllocator::is_allocated` to query whether a given id is currently
  allocated.

### Fixed

- [[#120]](https://github.com/rust-vmm/vm-allocator/pull/120): `IdAllocator::free_id` incorrectly accepted freeing `next_id` (an id that was
  never allocated), which could lead to the same id being allocated twice.

## [v0.1.3]

### Added 

- [[#102]](https://github.com/rust-vmm/vm-allocator/pull/102): Derived
  Clone for IdAllocator type.

## [v0.1.2]

### Added

- [[#40]](https://github.com/rust-vmm/vm-allocator/pull/40): Added serde
  support for IdAllocator and AddressAllocator.
- [[#99]](https://github.com/rust-vmm/vm-allocator/pull/99): Added APIs to
  get the base address and size of an AddressAllocator.

## [v0.1.1]

### Fixed

- [[#44]](https://github.com/rust-vmm/vm-allocator/pull/44): Fixed issue that
  did not allow the creating of inclusive ranges of size 1.

## [v0.1.0]

### Added

- Added types for (de)allocation of resources needed by the VMM during the VM
  lifetime.
