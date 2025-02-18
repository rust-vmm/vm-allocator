# Changelog

## Upcoming version

### Added

- Added `available()` API in `AddressAllocator` to allow
  getting the available memories after `allocate/free()`s

### Changed
### Fixed
### Removed
### Deprecated

## [v0.1.1]

### Fixed

- [[#44]](https://github.com/rust-vmm/vm-allocator/pull/44): Fixed issue that
  did not allow the creating of inclusive ranges of size 1.

## [v0.1.0]

### Added

- Added types for (de)allocation of resources needed by the VMM during the VM
  lifetime.
