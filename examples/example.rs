#![feature(inclusive_range)]
#![feature(inclusive_range_syntax)]
extern crate range_set;

use range_set::RangeSet;
use std::ops::RangeInclusive;

fn main() {
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
}
