extern crate range_set;

use range_set::{range_set, RangeSet};
use std::ops::RangeInclusive;

fn main() {
  range_set::report_sizes();  // report some sizes of various range set types

  let mut s = RangeSet::<[RangeInclusive <u32>; 1]>::from (0..=2);
  println!("s: {s:?}");
  assert!(!s.spilled());

  assert!(s.insert_range (8..=10).is_none());
  println!("s: {s:?}");
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![0,1,2,8,9,10]);

  assert_eq!(s.insert_range (3..=12), Some (RangeSet::from (8..=10)));
  println!("s: {s:?}");
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);

  assert_eq!(s.remove_range (0..=2), Some (RangeSet::from (0..=2)));
  println!("s: {s:?}");
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![3,4,5,6,7,8,9,10,11,12]);

  assert_eq!(s.remove_range (7..=9), Some (RangeSet::from (7..=9)));
  println!("s: {:?}", s.as_ref());
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![3,4,5,6,10,11,12]);

  assert_eq!(s.remove_range (6..=9), Some (RangeSet::from (6..=6)));
  println!("s: {s:?}");
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![3,4,5,10,11,12]);

  assert_eq!(s.remove_range (5..=10),
    Some (RangeSet::from_valid_ranges (&[5..=5, 10..=10]).unwrap()));
  println!("s: {s:?}");
  assert!(s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![3,4,11,12]);

  assert_eq!(s.remove_range (5..=20), Some (RangeSet::from (11..=12)));
  println!("s: {s:?}");
  assert!(s.spilled());   // stays spilled
  s.shrink_to_fit();      // manually un-spill
  assert!(!s.spilled());  // no longer spilled
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![3,4]);

  assert_eq!(s.remove_range (0..=10), Some (RangeSet::from (3..=4)));
  println!("s: {s:?}");
  assert!(!s.spilled());
  let v : Vec <u32> = s.iter().collect();
  assert_eq!(v, vec![]);

  let s = RangeSet::<[_; 4]>::from_ranges ([0..=3, 6..=10]);
  println!("s: {s:?}");
  let s = range_set!(0..=3, 6..=10);
  println!("s: {s:?}");
  println!("s.len(): {}", s.len());
  assert_eq!(s.len(), 9);
  let s = range_set!(0, 1, 2, 2, 3, 6, 7, 8, 8, 9, 10);
  println!("s: {s:?}");
  let s = range_set![0..=(u32::MAX)];
  println!("s: {s:?}");
  let mut s = range_set![];
  s.insert_range(0..=u32::MAX);
  s.insert_range(0..=0);
  println!("s: {s:?}");
  let mut s = range_set![];
  s.insert_range(0..=0);
  s.insert_range(0..=u32::MAX);
  println!("s: {s:?}");
  let mut s = range_set![250..=(u8::MAX)];
  println!("s: {s:?}");
  s.remove_range (252..=253);
  s.remove_range (254..=254);
  s.remove_range (255..=255);
  println!("s: {s:?}");
}
