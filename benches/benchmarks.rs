use criterion::{criterion_group, criterion_main, Criterion};
use vm_allocator::*;

const MIN: u32 = 0;
const MAX: u32 = 100;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("IdAllocator::new", |b| {
        b.iter(|| IdAllocator::new(MIN, MAX).unwrap())
    });
    c.bench_function("IdAllocator::new_unchecked", |b| {
        b.iter(|| IdAllocator::new_unchecked(MIN, MAX))
    });
    c.bench_function("IdAllocator::allocate_id", move |b| {
        b.iter_with_setup(
            || IdAllocator::new(MIN, MAX).unwrap(),
            |mut allocator| {
                allocator.allocate_id().unwrap();
            },
        )
    });
    c.bench_function("IdAllocator::allocate_id_unchecked", |b| {
        b.iter_with_setup(
            || IdAllocator::new_unchecked(MIN, MAX),
            |mut allocator| {
                allocator.allocate_id_unchecked();
            },
        )
    });
    c.bench_function("IdAllocator::free_id", |b| {
        b.iter_with_setup(
            || {
                let mut allocator = IdAllocator::new(MIN, MAX).unwrap();
                allocator.allocate_id().unwrap();
                allocator
            },
            |mut allocator| {
                allocator.free_id(MIN).unwrap();
            },
        )
    });
    c.bench_function("IdAllocator::free_id_unchecked", |b| {
        b.iter_with_setup(
            || {
                let mut allocator = IdAllocator::new_unchecked(MIN, MAX);
                allocator.allocate_id_unchecked();
                allocator
            },
            |mut allocator| {
                allocator.free_id_unchecked(MIN);
            },
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
