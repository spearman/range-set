# `range-set`

> Store a collection of contiguous `PrimInt` values as inclusive ranges using
> generic `SmallVec` storage

This is useful when you want to process elements in order when they are not
quite perfectly contiguous. Having a generic `smallvec::Array` parameter allows
choosing how many ranges will fit on the stack before spilling over onto the
heap:

```rust
let mut s = RangeSet::<[RangeInclusive <u8>; 1]>::from (0..=2);
println!("s: {:?}", s);
assert!(!s.spilled());

assert!(s.insert_range (8..=10).is_none());
println!("s: {:?}", s);
assert!(s.spilled());
let v : Vec <u8> = s.iter().collect();
assert_eq!(v, vec![0,1,2,8,9,10]);

assert_eq!(s.insert_range (3..=12), Some (RangeSet::from (8..=10)));
println!("s: {:?}", s);
assert!(!s.spilled());
let v : Vec <u8> = s.iter().collect();
assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);
```

## Usage

TODO

## Memory usage characteristics

The top-level `report` function will report byte sizes for various sizes of
integers and array sizes. An program calling this function can be found in
`./examples/example.rs`. Example output:

```
RangeSet report...
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
...RangeSet report
```

As can be seen, using this for byte ranges is not a good idea since the minimum
usage is 32 bytes which is enough to store the full range of 256 values as
individual bits (32 * 8 = 256).
