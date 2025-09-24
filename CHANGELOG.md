# Changelog

## Upcoming version

### Added

- Added `used()` API in `AddressAllocator` to allow
  getting the used memories after `allocate/free()`s

### Changed
### Fixed
### Removed
### Deprecated

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
