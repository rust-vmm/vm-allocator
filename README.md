# vm-allocator crate

## Design
vm-allocator is designed about resource and resource allocator being responsible
for system resources allocation for virtual machine(VM).

It provides different kinds of resources that might be used by VM, such as
memory-maped I/O address space, port I/O address space, legacy IRQ numbers, MSI/MSI-X
vectors, device instance id, etc. All these resources should be implemented with
allocation and freeing mechanism in this crate, in order to make VMM easier to
construct.

Main components are listed below.
- A `Resource` trait representing for all kinds of resources.
```rust
pub trait Resource {}
```

- A `ResourceSize` trait representing for all kinds of resource size.
```rust
pub trait ResourceSize {}
```

- A `ResourceAllocator` trait representing for all kinds of resources allocation, freeing
and updating.
```rust
pub trait ResourceAllocator<T: Resource, S: ResourceSize> {
    /// Allocate some resource with given `resource` and `size`.
    ///
    /// # Arguments
    ///
    /// * `resource`: resource to be allocate.
    /// * `size`: resource size of allocation request.
    fn allocate(
        &mut self,
        resource: Option<T>,
        size: S,
   ) -> Result<T, Error>;

    /// Free resource specified by given `resource` and `size`.
    ///
    /// # Arguments
    ///
    /// * `resource`: resource to be free.
    /// * `size`: resource size of free request.
    fn free(&mut self, resource: T, size: S);

    /// Update resource, freeing the old one and allocating a new range.
    ///
    /// This is mostly used when guest allocated some resources or reprogrammed,
    /// so the new allocated resources should be marked as used, and the preallocated
    /// one should be freed (if has). 
    ///
    /// # Arguments
    ///
    /// * `old_resource`: old resource to be free or no such preallocated resources.
    /// * `old_size`: old resource size of free request or no such preallocated resources.
    /// * `resource`: resource to be free.
    /// * `size`: resource size of free request.
    fn update(&mut self, old_resource: Option<T>, old_size: Option<S>, new_resource: T, new_size: S);
}
```

Different kinds of resources and its allocators should implement the three traits. Take
address space resource for example.

```rust
impl Resource for GuestAddress {}

// This should be implemented for u64.
// Otherwise implementing for GuestUsize (aka. <GuestAddress as AddressValue>::V)
// would impact other implementation such as instance id since compiler
// doesn't know real type of V.
impl ResourceSize for u64 {}

pub struct AddressAllocator {
    base: GuestAddress,
    end: GuestAddress,
    alignment: GuestUsize,
    ranges: BTreeMap<GuestAddress, GuestUsize>,
}

impl ResourceAllocator<GuestAddress, GuestUsize> for AddressAllocator {
    /// Allocates a range of addresses from the managed region.
    fn allocate(
        &mut self,
        address: Option<GuestAddress>,
        size: GuestUsize,
    ) -> Result<GuestAddress> {...}

    /// Free an already allocated address range.
    fn free(&mut self, address: GuestAddress, size: GuestUsize) {...}

    /// Update an address range with a new one.
    fn update(&mut self, old_resource: Option<T>, old_size: Option<S>, new_resource: T, new_size: S) {...}
```

Another resource being used by VMM is unsigned integer resource,
like IRQ numbers including legacy IRQ numbers and MSI/MSI-X vectors, device instance id.

```rust
impl Resource for u32 {}
impl ResourceSize for u32 {}
pub struct IdAllocator {
    start: u32,
    end: u32,
    used: Vec<u32>,
}
impl ResourceAllocator<u32, u32> for IdAllocator {...}
```

### Design Note:

VMM is responsible for system level resources allocation, and some principles and
special cases should be taken into account.

- Vmm probably need record which kinds of resources it has, like how many IRQ numbers, how
many IO address ranges. 

Let VMM design a `SystemAllocator` struct because only VMM knows exactly which resources it
needs and whether it needs thread safe.

Meanwhile, different resource instances are not suggested to being put together using like
a hashmap `Hashmap<String, Arc<Mutex<ResourceAllocator>>>`. This would make allocation
harder to know the exact resource type and value.

- Vmm probably need a `ResourceMap` struct recording the resources belong to each device,
so that VMM could inform vm-allocator crate to update the resource map changing and do
unregistering/freeing work once the device lifetime comes to the end.

```rust
/// Describe a device resource set.
pub struct ResourceSet {
    pub instance_id: u32,
    pub irq: u32,
    pub io_resources: Vec<IoResource>,
}

/// Describe a device resource mapping.
pub struct ResourceMap {
    pub map: BTreeMap<Arc<Mutex<dyn Device>>, ResourceSet>, 
}

pub struct Vmm {
    ...
    pub resource_map: ResourceMap,
    ...
}
```

- Vmm should pass some resources/allocators (e.g. `SystemAllocator` struct) into each
Vcpu thread, in case that guest might change some resources usage for devices, like PCI BAR
reprogramming, MSI/MSI-X vectors informing by a write operation from guest.

## Usage

This crate would be implemented by VMM according to what kinds of resources it needs on demand.
For example, simple VMM might need only IRQ numbers and device instance ids, and they don't quite
need manage IO address space. In suce case, they can simply define the two instances as a
type of `IdAllocator`.

The VMM decides whether it needs a collection of resources which might be called like
`SystemAllocator`. Meanwhile, the thread safe is ensured by VMM.

If a VMM needs a new type of resource other than address or integer, it can either implement
`Resource`, `ResourceSize` and `ResourceAllocator` traits for its newly defined resource struct,
or considering add this into vm-allocator crate later.

## Examples

This demonstrates how VMM uses vm-allocator crate to manage resources.
Firstly, assuming VMM implements a SystemAllocator for collecting resources.

```rust
//! system_allocator.rs
//! Assuming the VMM only needs three resources: instance_id, irq, mmio address space.

use vm-allocator::{Resource, ResourceAllocator, ResourceSize};
use vm-allocator::{AddressAllocator, IdAllocator};

// This would be as a member of Vmm.
// A Clone needs to be passed into every Vcpu thread, because when resources are changed
// by guest, this needs to be changed accordingly.
//
// A design of Arc<Mutex<>> works but it really depends on design and allocator type.
pub struct SystemAllocator {
    pub instance_id: Arc<Mutex<IdAllocator>>,
    pub irq: Arc<Mutex<IdAllocator>>,
    pub mmio_range: Arc<Mutex<AddressAllocator>>,
}

impl SystemAllocator {
    pub fn new(some_parameters) -> Self {
    }

    // MSI/MSI-X vectors are allocated/specified by guest driver, so the virtual interrupt
    // number resource needs to be updated after device receives the information, 
    // by a BAR writing operation.
    pub fn update_irq(&mut self, vector: u32) -> Result<()> {
        // Normally, MSI/MSI-X vectors are allocated from non-used kernel interrupt resource.
        // Otherwise, this interrupt should not be expected by kernel.
        self.irq.lock().expect("failed").allocate(Some(vector), 1);
    }

    /// PCI BAR might be reprogrammed by guest kernel.
    pub fn update_mmio_addr(&mut self, old_addr: GuestAddress, old_size: GuestUsize,
        new_addr: GuestAddress, new_size: GuestUsize) -> Result<()> {
        // Check if old_addr exists and free it.
        self.mmio_range.lock().expect("failed").free(old_addr, old_size);
        // Check if new_addr is valid and allocate it.
        self.mmio_range.lock().expect("failed").allocate(new_addr, new_size);
    }

    /// Allocate an instance id for device.
    pub fn allocate_device_id(&mut self) -> Result<u32> {...}

    pub fn free_device_id(&mut self, id: u32) {...}

    /// Allocate an IRQ number.
    ///
    /// * `irq`: specify a specific number or any value.
    pub fn allocate_irq(&mut self, irq: Option<u32>) -> Result<u32> {...}

    pub fn free_irq(&mut self, id: u32) {...}

    /// Allocate mmio address and size.
    pub fn allocate_mmio_addr(&mut self, addr: Option<GuestAddress>, size: GuestUsize) -> Result<GuestAddress> {...}

    pub fn free_mmio_addr(&mut self, addr: GuestAddress, size: GuestUsize) {...}
    ...
}
```

The VMM initalization work flow is as follows.

```rust
use vm_allocator::{Resource, ResourceAllocator, ResourceSize};
use vm_device::DeviceManager;

let vmm = Vmm::new();
// Other initialization related to the vmm
...
// Initialize the SystemAllocator and add Resource Allocator to it.
let sys_alloc = SystemAllocator::new(some_parameters);

// Initialize the DeviceManager.
let dev_mgr = DeviceManager::new();

// Initialize a PCI device.
let pci_dev = Arc::new(Mutex::new(DummyPciDevice::new()));

// Allocate IRQ, instance id, MMIO space for the dummy pci device.
let id = sys_alloc.allocate_instance_id().unwrap();
let irq = sys_alloc.allocate_irq(None).unwrap();
let addr = sys_alloc.allocate_mmio_addr(None, 0x100);

// The VMM needs a structure to store all the resources mapping to device instance
// used for unregistering and resource freeing.
vmm.resource_map.insert(ResourceSet{id, irq, Range{addr, 0x100}}, pci_dev.clone());

// Insert the device into DeviceManager with preallocated resources.
dev_mgr.register_device(pci_dev, id, Some(irq), vec![addr]);

// Other operation for vmm.
...

// Unregister this device like unhotplug case.

// Firstly, get all the resources belong to the unplugged device.
let set = vmm.resource_map.get(pci_dev.clone());

// Unregister this device from DeviceManager.
dev_mgr.unregister_device(set.id);

// Free resources of this device.
sys_alloc.free_device_id(set.id);
sys_alloc.free_irq(set.irq);
sys_alloc.free_mmio_addr(set.addr, set.size);

```

Some resources changing might happen during vcpu running. Take MSI vector for example.
```rust
pub struct Vcpu {
    fd: VcpuFd,
    id: u8,
    device_manager: Arc<Mutex<DeviceManager>>,
    system_allocator: SystemAllocator,
}

pub enum ResourceChange {
    NoChange,
    IrqOccupying(irq),
    IoReprogramming(addr, size), 
}

impl Vcpu {
    // Runs the VCPU until it exits, returning the reason.
    pub fn run(&self) -> Result<()> {
        match self.fd.run() {
            VcpuExit::MmioWrite(addr, data) => {
                // Guest write MSI vector information to device BAR. 
                match self.device_manager.mmio_bus.write(GuestAddress{addr as u64}, data) {
                    // A MSI vector set is written back from guest
                    // Check if there is resource changing.
                    ResourceChange::IrqOccupying(irq) => {
                        // Call vm_allocator to update the irq resource.
                        self.system_allocator.update_irq(irq).map_err();
                        // Call vm_device to update.
                        self.device_manager.update_irq(irq).map_err();
                    },
                    // PCI BAR is reprogrammed by guest.
                    ResourceChange::IoReprogramming(addr, size) => {
                        // Call vm_allocator to update the io resource.
                        self.system_allocator.update_mmio_addr(addr, size).map_err();
                        // Call vm_device to update.
                        self.device_manager.update_mmio_addr(addr, size).map_err();
                    },
                    ResourceChange::NoChange => Ok(()),
                }
            }
            ...
        }
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
