# `range-set`

> Store collections of `PrimInt` values as inclusive ranges using generic
> `SmallVec`-backed storage.

[Documentation](https://docs.rs/range-set)

A generic `smallvec::Array` parameter allows choosing how many ranges will fit
on the stack before spilling over onto the heap:

```rust
let mut s = RangeSet::<[RangeInclusive <u32>; 1]>::from (0..=2);
println!("s: {:?}", s);
assert!(!s.spilled());

assert!(s.insert_range (8..=10).is_none());
println!("s: {:?}", s);
assert!(s.spilled());
let v : Vec <u32> = s.iter().collect();
assert_eq!(v, vec![0,1,2,8,9,10]);

assert_eq!(s.insert_range (3..=12), Some (RangeSet::from (8..=10)));
println!("s: {:?}", s);
assert!(!s.spilled());
let v : Vec <u32> = s.iter().collect();
assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);
```

This is most useful with large blocks of not-quite contiguous data that should
be traversed in-order.

## Usage

Inclusive ranges are an unstable Rust feature (as of `rustc` 1.26) so they must
be enabled in the crate root:

```rust
#![feature(inclusive_range)]

extern crate range_set;
```

```rust
  use range_set::RangeSet;
  use std::ops::RangeInclusive;
  let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from_ranges (vec![
    1..=100,
    500..=1000
  ].into()).unwrap();
  s.insert (200);
  s.insert (400..=499);
  assert_eq!(s, RangeSet::from_ranges (vec![
    1..=100,
    200..=200,
    400..=1000
  ].into()).unwrap());
```

See `./examples/example.rs` and documentation for more examples.

## On-stack sizes

The top-level `report_sizes` function will report byte sizes for various
combinations of integer types and array sizes. A program calling this function
can be found in `./examples/example.rs`. Example output:

```
RangeSet report sizes...
  size of RangeSet <[RangeInclusive <u8>; 1]>: 32
  size of RangeSet <[RangeInclusive <u16>; 1]>: 32
  size of RangeSet <[RangeInclusive <u32>; 1]>: 32
  size of RangeSet <[RangeInclusive <u64>; 1]>: 32
  size of RangeSet <[RangeInclusive <usize>; 1]>: 32
  size of RangeSet <[RangeInclusive <u8>; 2]>: 32
  size of RangeSet <[RangeInclusive <u16>; 2]>: 32
  size of RangeSet <[RangeInclusive <u32>; 2]>: 32
  size of RangeSet <[RangeInclusive <u64>; 2]>: 48
  size of RangeSet <[RangeInclusive <usize>; 2]>: 48
  size of RangeSet <[RangeInclusive <u8>; 4]>: 32
  size of RangeSet <[RangeInclusive <u16>; 4]>: 32
  size of RangeSet <[RangeInclusive <u32>; 4]>: 48
  size of RangeSet <[RangeInclusive <u64>; 4]>: 80
  size of RangeSet <[RangeInclusive <usize>; 4]>: 80
  size of RangeSet <[RangeInclusive <u8>; 8]>: 32
  size of RangeSet <[RangeInclusive <u16>; 8]>: 48
  size of RangeSet <[RangeInclusive <u32>; 8]>: 80
  size of RangeSet <[RangeInclusive <u64>; 8]>: 144
  size of RangeSet <[RangeInclusive <usize>; 8]>: 144
  size of RangeSet <[RangeInclusive <u8>; 16]>: 48
  size of RangeSet <[RangeInclusive <u16>; 16]>: 80
  size of RangeSet <[RangeInclusive <u32>; 16]>: 144
  size of RangeSet <[RangeInclusive <u64>; 16]>: 272
  size of RangeSet <[RangeInclusive <usize>; 16]>: 272
...RangeSet report sizes
```

Storing `u8` (byte) ranges is not a good idea since the minimum size (to store
a single range on the stack) is 32 bytes which is enough to store the full
range of 256 values as individual bits (32 * 8 = 256).

## Operations

Since the ranges are stored in sorted order, binary search is used when
inserting and removing values.
