# `range-set`

> Store collections of `PrimInt` values as inclusive ranges using generic
> `SmallVec`-backed storage.

[Documentation](https://docs.rs/range-set)

A generic `smallvec::Array` parameter allows choosing how many ranges will fit
on the stack before spilling over onto the heap:

```rust
let mut s = range_set![0..=2; 1];
println!("s: {:?}", s);
assert!(!s.spilled());

assert!(s.insert_range (8..=10).is_none());
println!("s: {:?}", s);
assert!(s.spilled());
let v : Vec <u32> = s.iter().collect();
assert_eq!(v, vec![0,1,2,8,9,10]);

assert_eq!(s.insert_range (3..=12), Some (range_set![8..=10; 1]));
s.shrink_to_fit();
println!("s: {:?}", s);
assert!(!s.spilled());
let v : Vec <u32> = s.iter().collect();
assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);
```

This is most useful with large blocks of not-quite contiguous data that should
be traversed in-order.

## Usage

```rust
  use range_set::{range_set, RangeSet};
  let mut s = RangeSet::<[_; 2]>::from_ranges ([1..=100, 500..=1000]);
  s.insert (200);
  s.insert_range (400..=499);
  assert_eq!(s, range_set![1..=100, 200..=200, 400..=1000]);
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
