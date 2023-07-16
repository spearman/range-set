extern crate range_set;
use range_set::{range_set, RangeSet};

fn main() {
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

  let mut s = RangeSet::<[_; 2]>::from_ranges ([1..=100, 500..=1000]);
  s.insert (200);
  s.insert_range (400..=499);
  assert_eq!(s, range_set![1..=100, 200..=200, 400..=1000]);
}
