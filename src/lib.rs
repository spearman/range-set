//! `RangeSet` container type.
//!
//! `RangeSet` stores collections of `PrimInt` values as inclusive ranges using
//! generic [`SmallVec`](https://docs.rs/smallvec)-backed storage. This means
//! that a certain amount of ranges will fit on the stack before spilling over
//! to the heap.

extern crate num_traits;
#[cfg(feature = "derive_serdes")]
extern crate serde;
extern crate smallvec;

pub mod range_compare;

pub use range_compare::{
  RangeCompare, RangeDisjoint, RangeIntersect, range_compare, intersection
};

use std::ops::RangeInclusive;
use num_traits::PrimInt;
use smallvec::SmallVec;

////////////////////////////////////////////////////////////////////////////////
//  structs                                                                   //
////////////////////////////////////////////////////////////////////////////////

/// A set of primitive integers represented as a sorted list of disjoint,
/// inclusive ranges.
///
/// The generic parameter specifies the type of on-stack array to be used in the
/// backing `SmallVec` storage.
///
/// ```
/// # use range_set::range_set;
/// let mut s = range_set![0..=2; 1];
/// assert!(!s.spilled());
///
/// assert_eq!(s.insert_range (8..=10), None);
/// assert_eq!(s, range_set![0..=2, 8..=10]);
/// assert!(s.spilled());
///
/// assert_eq!(s.insert_range (3..=12), Some (range_set![8..=10; 1]));
/// assert_eq!(s, range_set![0..=12]);
/// assert!(s.spilled());  // once spilled, stays spilled
/// 
/// s.shrink_to_fit();  // manually un-spill
/// assert_eq!(s, range_set![0..=12]);
/// assert!(!s.spilled());
/// ```
#[derive(Clone, Debug, Eq)]
pub struct RangeSet <A> where
  A       : smallvec::Array + Eq + std::fmt::Debug,
  A::Item : Clone + Eq + std::fmt::Debug
{
  ranges : SmallVec <A>
}

/// Iterates over elements of the `RangeSet`
pub struct Iter <'a, A, T> where
  A : 'a + smallvec::Array <Item=RangeInclusive <T>> + Eq + std::fmt::Debug,
  T : 'a + PrimInt + std::fmt::Debug
{
  range_set   : &'a RangeSet <A>,
  range_index : usize,
  range       : RangeInclusive <T>
}

////////////////////////////////////////////////////////////////////////////////
//  functions                                                                 //
////////////////////////////////////////////////////////////////////////////////

/// Tests a slice of ranges for validity as a range set: the element ranges
/// must be properly disjoint (not adjacent) and sorted.
///
/// ```
/// # use range_set::valid_range_slice;
/// let mut v = Vec::new();
/// assert!(valid_range_slice (&v));
/// v.push (0..=3);
/// assert!(valid_range_slice (&v));
/// v.push (6..=10);
/// assert!(valid_range_slice (&v));
/// v.push (0..=1);
/// assert!(!valid_range_slice (&v));
/// ```
pub fn valid_range_slice <T, V> (ranges : V) -> bool where
  T : PartialOrd + PrimInt,
  V : AsRef <[RangeInclusive <T>]>
{
  let ranges = ranges.as_ref();
  if !ranges.is_empty() {
    for i in 0..ranges.len()-1 { // safe to subtract here since non-empty
      let this = &ranges[i];
      let next = &ranges[i+1];  // safe to index
      if this.is_empty() || next.is_empty() {
        return false
      }
      if *next.start() <= *this.end()+T::one() {
        return false
      }
    }
  }
  true
}

/// Report some sizes of various range set types
pub fn report_sizes() {
  use std::mem::size_of;
  println!("RangeSet report sizes...");

  println!("  size of RangeSet <[RangeInclusive <u32>; 1]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 1]>: {}",
    size_of::<RangeSet <[RangeInclusive <u16>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 1]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 1]>: {}",
    size_of::<RangeSet <[RangeInclusive <u64>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 1]>: {}",
    size_of::<RangeSet <[RangeInclusive <usize>; 1]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 2]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 2]>: {}",
    size_of::<RangeSet <[RangeInclusive <u16>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 2]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 2]>: {}",
    size_of::<RangeSet <[RangeInclusive <u64>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 2]>: {}",
    size_of::<RangeSet <[RangeInclusive <usize>; 2]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 4]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 4]>: {}",
    size_of::<RangeSet <[RangeInclusive <u16>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 4]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 4]>: {}",
    size_of::<RangeSet <[RangeInclusive <u64>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 4]>: {}",
    size_of::<RangeSet <[RangeInclusive <usize>; 4]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 8]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 8]>: {}",
    size_of::<RangeSet <[RangeInclusive <u16>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 8]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 8]>: {}",
    size_of::<RangeSet <[RangeInclusive <u64>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 8]>: {}",
    size_of::<RangeSet <[RangeInclusive <usize>; 8]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 16]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 16]>: {}",
    size_of::<RangeSet <[RangeInclusive <u16>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 16]>: {}",
    size_of::<RangeSet <[RangeInclusive <u32>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 16]>: {}",
    size_of::<RangeSet <[RangeInclusive <u64>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 16]>: {}",
    size_of::<RangeSet <[RangeInclusive <usize>; 16]>>());

  println!("...RangeSet report sizes");
}

////////////////////////////////////////////////////////////////////////////////
//  impls                                                                     //
////////////////////////////////////////////////////////////////////////////////

// the majority of the logic for modifying range sets are the insert_range and
// remove_range methods
//
// there are some helper functions with additional logic such as the
// binary_search functions
impl <A, T> RangeSet <A> where
  A : smallvec::Array <Item=RangeInclusive <T>> + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug
{
  /// New empty range set
  /// 
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// 
  /// let s = RangeSet::<[RangeInclusive<u32>; 2]>::new();
  /// assert_eq!(s, range_set![; 2]);
  /// ```
  #[inline]
  pub fn new() -> Self {
    RangeSet {
      ranges: SmallVec::new()
    }
  }

  /// New empty range set with the internal smallvec initialized with the given
  /// initial capacity
  /// 
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// 
  /// let s = RangeSet::<[RangeInclusive<u32>; 2]>::with_capacity(50);
  /// assert_eq!(s, range_set![; 2]);
  /// ```
  #[inline]
  pub fn with_capacity (capacity : usize) -> Self {
    RangeSet {
      ranges: SmallVec::with_capacity (capacity)
    }
  }

  /// Returns a new range set if the given smallvec is valid and sorted.
  /// (See [`valid_range_slice`])
  /// 
  /// ```
  /// # extern crate smallvec;
  /// # use range_set::{RangeSet, range_set};
  /// # use smallvec::SmallVec;
  /// # use std::ops::RangeInclusive;
  /// 
  /// let v: SmallVec<[RangeInclusive<u32>; 5]> = SmallVec::from_vec(vec![5..=10, 12..=12]);
  /// assert_eq!(RangeSet::from_smallvec(v), Some(range_set![5..=10, 12; 5]));
  /// 
  /// let v: SmallVec<[RangeInclusive<u32>; 5]> = SmallVec::from_vec(vec![5..=10, 2..=3, 12..=12]);
  /// assert_eq!(RangeSet::from_smallvec(v), None);
  /// 
  /// let v: SmallVec<[RangeInclusive<u32>; 5]> = SmallVec::from_vec(vec![5..=10, 11..=12]);
  /// assert_eq!(RangeSet::from_smallvec(v), None);
  /// ```
  pub fn from_smallvec (ranges : SmallVec <A>) -> Option <Self> {
    if valid_range_slice (ranges.as_slice()) {
      Some (RangeSet { ranges })
    } else {
      None
    }
  }

  /// Unchecked version of [`from_smallvec`](Self::from_smallvec)
  pub unsafe fn from_raw_parts (ranges : SmallVec <A>) -> Self {
    debug_assert!(valid_range_slice (ranges.as_slice()));
    RangeSet { ranges }
  }

  /// Returns a new range set if the given slice of ranges is valid and sorted
  /// (See [`valid_range_slice`])
  pub fn from_valid_ranges <V : AsRef <[RangeInclusive <T>]>> (ranges : V)
    -> Option <Self>
  {
    if valid_range_slice (&ranges) {
      let ranges = SmallVec::from (ranges.as_ref());
      Some (RangeSet { ranges })
    } else {
      None
    }
  }

  /// Constructs a new range set from an array or vector of inclusive ranges.
  ///
  /// This method has been specially optimized for non-overlapping, non-
  /// adjacent ranges in ascending order. See [`valid_range_slice`].
  pub fn from_ranges <V : AsRef <[RangeInclusive <T>]>> (ranges : V) -> Self {
    let mut ret = Self::new();
    for range in ranges.as_ref() {
      ret.insert_range_optimistic(range.clone());
    }
    ret
  }

  /// Constructs a new range set from a slice of numbers.
  ///
  /// This method has been specially optimized for deduplicated arrays, sorted
  /// in ascending order. Construction time is `O(n)` for these arrays.
  ///
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  ///
  /// let reference = range_set![1..=4, 6, 8..=10];
  ///
  /// // Optimal ordering. Special O(n) applies.
  /// let good = RangeSet::<[RangeInclusive<u32>; 4]>::from_elements([1, 2, 3, 4, 6, 8, 9, 10]);
  ///
  /// // Random ordering. Very expensive.
  /// let bad = RangeSet::<[RangeInclusive<u32>; 4]>::from_elements([2, 9, 6, 8, 1, 4, 10, 3, 4, 8]);
  ///
  /// assert_eq!(good, reference);
  /// assert_eq!(bad, reference);
  /// ```
  pub fn from_elements <V : AsRef <[T]>> (elements : V) -> Self {
    let mut current_range : Option<(T, T)> = None;
    let mut set = Self::new();

    for &element in elements.as_ref() {
      // current_range is updated every iteration.
      current_range = if let Some((start, end)) = current_range {
        if element == end+T::one() {
          Some((start, element))
        } else {
          set.insert_range_optimistic(start..=end);
          Some((element, element))
        }
      } else {
        Some((element, element))
      };
    }

    if let Some((start, end)) = current_range {
      set.insert_range_optimistic(start..=end);
    }

    set
  }

  /// Check if range set is empty
  #[inline]
  pub fn is_empty (&self) -> bool {
    self.ranges.is_empty()
  }

  /// Clears the range set
  #[inline]
  pub fn clear (&mut self) {
    self.ranges.clear()
  }

  /// Converts into the internal smallvec
  #[inline]
  pub fn into_smallvec (self) -> SmallVec <A> {
    self.ranges
  }

  /// Returns true if the element is contained in this set.
  ///
  /// ```
  /// # use range_set::range_set;
  /// let mut set = range_set![2..=5, 10..=70, 72, 74..=80];
  ///
  /// assert!(set.contains(2));
  /// assert!(set.contains(3));
  /// assert!(set.contains(33));
  /// assert!(set.contains(72));
  /// assert!(set.contains(80));
  ///
  /// assert!(!set.contains(0));
  /// assert!(!set.contains(6));
  /// assert!(!set.contains(71));
  /// assert!(!set.contains(122));
  /// ```
  pub fn contains (&self, element : T) -> bool {
    self.contains_range(element..=element)
  }

  /// Returns true if all the elements of `range` are contained in this set.
  ///
  /// ```
  /// # use range_set::range_set;
  /// let mut set = range_set![2..=5, 10..=70, 72, 74..=80];
  ///
  /// assert!(set.contains_range(2..=4));
  /// assert!(set.contains_range(3..=5));
  /// assert!(set.contains_range(33..=50));
  /// assert!(set.contains_range(75..=80));
  ///
  /// assert!(!set.contains_range(0..=6));
  /// assert!(!set.contains_range(3..=6));
  /// assert!(!set.contains_range(10..=72));
  /// assert!(!set.contains_range(50..=75));
  /// assert!(!set.contains_range(71..=72));
  /// assert!(!set.contains_range(122..=200));
  /// ```
  pub fn contains_range (&self, range : A::Item) -> bool {
    self.contains_range_ref(&range)
  }

  /// Returns `true` if the set is a superset of another, i.e., `self` contains
  /// at least all the elements in `other`.
  ///
  /// ```
  /// # use range_set::range_set;
  ///
  /// let main = range_set![3..=15];
  ///
  /// assert_eq!(range_set![0..=15].is_superset(&main), true);
  /// assert_eq!(main.is_superset(&main), true);
  /// assert_eq!(range_set![0..=7, 9..=15].is_superset(&main), false);
  /// ```
  pub fn is_superset (&self, other : &Self) -> bool {
    other.is_subset(self)
  }

  /// Returns `true` if the set is a subset of another, i.e., `other` contains
  /// at least all the elements in `self`.
  ///
  /// ```
  /// # use range_set::range_set;
  ///
  /// let main = range_set![3..=15];
  ///
  /// assert_eq!(range_set![6..=10].is_subset(&main), true);
  /// assert_eq!(main.is_subset(&main), true);
  /// assert_eq!(range_set![6..=10, 99].is_subset(&main), false);
  /// ```
  pub fn is_subset (&self, other : &Self) -> bool {
    self.ranges.iter().all(|range| other.contains_range_ref (range))
  }

  /// Returns the largest element in the set, or `None` if the set is empty.
  /// 
  /// ```
  /// # use range_set::{range_set, RangeSet};
  /// # use std::ops::RangeInclusive;
  /// 
  /// assert_eq!(range_set![5..=8].max(), Some(8));
  /// assert_eq!(range_set![2..=3, 5..=8].max(), Some(8));
  /// assert_eq!(range_set![5..=8, 10].max(), Some(10));
  /// assert_eq!(RangeSet::<[RangeInclusive<u32>; 4]>::new().max(), None);
  /// ```
  pub fn max (&self) -> Option <T> {
    self.ranges.last().map(|r| *r.end())
  }

  /// Returns the smallest element in the set, or `None` if the set is empty.
  /// 
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// 
  /// assert_eq!(range_set![5..=8].min(), Some(5));
  /// assert_eq!(range_set![2..=3, 5..=8].min(), Some(2));
  /// assert_eq!(range_set![5..=8, 10].min(), Some(5));
  /// assert_eq!(RangeSet::<[RangeInclusive<u32>; 4]>::new().min(), None);
  /// ```
  pub fn min (&self) -> Option <T> {
    self.ranges.first().map(|r| *r.start())
  }

  /// Insert a single element, returning true if it was successfully inserted
  /// or else false if it was already present
  ///
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// 
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::new();
  /// assert!(s.insert (4));
  /// assert_eq!(s, range_set![4..=4]);
  /// assert!(!s.insert (4));
  /// assert_eq!(s, range_set![4..=4]);
  /// assert!(s.insert (5));
  /// assert_eq!(s, range_set![4..=5]);
  /// assert!(s.insert (3));
  /// assert_eq!(s, range_set![3..=5]);
  /// assert!(s.insert (10));
  /// assert_eq!(s, range_set![3..=5, 10..=10]);
  /// ```
  pub fn insert (&mut self, element : T) -> bool {
    if let Some (_) = self.insert_range (element..=element) {
      false
    } else {
      true
    }
  }

  /// Remove a single element, returning true if it was successfully removed
  /// or else false if it was not present
  ///
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert!(s.remove (1));
  /// assert_eq!(s, range_set![0..=0, 2..=5]);
  /// assert!(!s.remove (1));
  /// assert_eq!(s, range_set![0..=0, 2..=5]);
  /// assert!(s.remove (4));
  /// assert_eq!(s, range_set![0..=0, 2..=3, 5..=5]);
  /// assert!(s.remove (3));
  /// assert_eq!(s, range_set![0..=0, 2..=2, 5..=5]);
  /// assert!(s.remove (2));
  /// assert_eq!(s, range_set![0..=0, 5..=5]);
  /// assert!(s.remove (0));
  /// assert_eq!(s, range_set![5..=5]);
  /// assert!(s.remove (5));
  /// assert!(s.is_empty());
  /// ```
  pub fn remove (&mut self, element : T) -> bool {
    if let Some (_) = self.remove_range (element..=element) {
      true
    } else {
      false
    }
  }

  /// Returns the intersected values if the range is not disjoint
  /// with the curret range set.
  ///
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.insert_range ( 3..=10), Some (range_set![3..=5; 2]));
  /// assert_eq!(s, range_set![0..=10]);
  /// assert_eq!(s.insert_range (20..=30), None);
  /// assert_eq!(s, range_set![0..=10, 20..=30]);
  /// ```
  pub fn insert_range (&mut self, range : A::Item) -> Option <Self> {
    if range.is_empty () {       // empty range
      return None
    }
    if self.ranges.is_empty() { // empty range set
      self.ranges.push (range);
      return None
    }
    let before = Self::binary_search_before_proper (self, &range);
    let after  = Self::binary_search_after_proper  (self, &range);
    match (before, after) {
      // no existing ranges are properly greater than or less than the range:
      // this means that both the first range and the last range are either
      // intersected with or adjacent to the given range, implying that the
      // range set will be fused to a single range containing the min and max
      // of the intersection of the given range and the existing range set
      (None, None) => {
        let isect = self.range_intersection (&range, 0..self.ranges.len());
        let new_range =
          std::cmp::min (*range.start(), *self.ranges[0].start())..=
          std::cmp::max (*range.end(),   *self.ranges[self.ranges.len()-1].end());
        self.ranges.clear();
        self.ranges.push (new_range);
        if !isect.is_empty() {
          Some (isect)
        } else {
          None
        }
      }
      // there exist some ranges that are properly less than the given range
      (Some (before), None) => {
        if before+1 == self.ranges.len() {  // push after last range
          self.ranges.push (range);
          None
        } else {  // otherwise merge into last range
          let isect
            = self.range_intersection (&range, before+1..self.ranges.len());
          self.ranges[before+1] =
            std::cmp::min (*range.start(), *self.ranges[before+1].start())..=
            std::cmp::max (*range.end(), *self.ranges[self.ranges.len()-1].end());
          self.ranges.truncate (before+2);
          if !isect.is_empty() {
            Some (isect)
          } else {
            None
          }
        }
      }
      // there exist some ranges that are properly greater than the given range
      (None, Some (after)) => {
        if after == 0 { // insert before first range
          self.ranges.insert (0, range);
          None
        } else {        // otherwise merge into first range
          let isect = self.range_intersection (&range, 0..after);
          self.ranges[0] =
            std::cmp::min (*range.start(), *self.ranges[0].start())..=
            std::cmp::max (*range.end(), *self.ranges[after - 1].end());
          self.ranges.as_mut_slice()[1..].rotate_left(after - 1);
          let new_len = self.ranges.len() - after + 1;
          self.ranges.truncate (new_len);
          if !isect.is_empty() {
            Some (isect)
          } else {
            None
          }
        }
      }
      // there are ranges both properly less than and properly greater than the
      // given range
      (Some (before), Some (after)) => {
        if before+1 == after {  // insert between ranges
          self.ranges.insert (before+1, range);
          None
        } else {                // otherwise merge with existing ranges
          let isect = self.range_intersection (&range, before+1..after);
          self.ranges[before+1] =
            std::cmp::min (*range.start(), *self.ranges[before+1].start())..=
            std::cmp::max (*range.end(), *self.ranges[after-1].end());
          // if there are more than one ranges between we must shift and truncate
          if 1 < after - before - 1 {
            self.ranges.as_mut_slice()[(before + 2)..]
              .rotate_left (after - before - 2);
            let new_len = self.ranges.len() - (after - before - 2);
            self.ranges.truncate (new_len);
          }
          if !isect.is_empty() {
            Some (isect)
          } else {
            None
          }
        }
      }
    }
  } // end fn insert_range

  /// This is like `insert_range`, but has O(1) runtime if `range` is placed at
  /// the end of the set.
  fn insert_range_optimistic (&mut self, range : A::Item) {
    if let Some(last) = self.ranges.last() {
      if *last.end()+T::one() < *range.start() {
        self.ranges.push(range);
      } else {
        // Fallback on normal insert, and discard the return value.
        self.insert_range(range);
      }
    } else {
      // Ranges is empty.
      self.ranges.push(range);
    }
  }

  /// Removes and returns the intersected elements, if there were any.
  ///
  /// ```
  /// # use range_set::{RangeSet, range_set};
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.remove_range (3..=3), Some (range_set![3; 2]));
  /// assert_eq!(s, range_set![0..=2, 4..=5]);
  /// assert_eq!(s.remove_range (0..=10), Some (range_set![0..=2, 4..=5; 2]));
  /// assert!(s.is_empty());
  /// ```
  pub fn remove_range (&mut self, range : A::Item) -> Option <Self> {
    if self.ranges.is_empty() || range.is_empty() {  // empty
      return None
    }
    let before = Self::binary_search_before (self, &range);
    let after  = Self::binary_search_after  (self, &range);
    // non-inclusive range of ranges to check for intersection
    let (isect_first, isect_last) = match (before, after) {
      (None, None)                  => (0, self.ranges.len()),
      (Some (before), None)         => (before+1, self.ranges.len()),
      (None, Some (after))          => (0, after),
      (Some (before), Some (after)) => (before+1, after)
    };
    let isect = self.range_intersection (&range, isect_first..isect_last);
    if isect.is_empty() {
      return None
    }

    // a split range is only possible if there was a single intersection
    if isect_last - isect_first == 1 {
      let single_range = self.ranges[isect_first].clone();
      if single_range.start() < range.start() &&
        range.end() < single_range.end()
      {
        let left  = *single_range.start()..=*range.start() - T::one();
        let right = *range.end() + T::one()..=*single_range.end();
        self.ranges[isect_first] = right;
        self.ranges.insert (isect_first, left);
        return Some (isect)
      }
    }

    // one or more range intersected: the range of intersected ranges will be
    // reduced to zero, one, or two ranges
    let first = self.ranges[isect_first].clone();
    let last  = self.ranges[isect_last-1].clone();

    let (remove_first, remove_last) = if
    // all intersected ranges removed: shift higher ranges down
      range.start() <= first.start() && last.end() <= range.end()
    {
      (isect_first, isect_last)
    // first intersected range remains but is shortened
    } else if first.start() < range.start() && last.end() <= range.end() {
      self.ranges[isect_first] =
        *self.ranges[isect_first].start()..=*range.start() - T::one();
      (isect_first+1, isect_last)
    // last intersected range remains but is shortened
    } else if range.start() <= first.start() && range.end() < last.end() {
      self.ranges[isect_last-1] =
        *range.end() + T::one()..=*self.ranges[isect_last-1].end();
      (isect_first, isect_last-1)
    // both first and last range remain and are shortened
    } else {
      debug_assert!(first.start() < range.start() && range.end() < last.end());
      self.ranges[isect_first] =
        *self.ranges[isect_first].start()..=*range.start() - T::one();
      self.ranges[isect_last-1] =
        *range.end()   + T::one()..=*self.ranges[isect_last-1].end();
      (isect_first+1, isect_last-1)
    };
    // remove ranges, shift later ranges and truncate
    for (i, index) in (remove_last..self.ranges.len()).enumerate() {
      self.ranges[remove_first+i] = self.ranges[index].clone();
    }
    let new_len = self.ranges.len() - (remove_last - remove_first);
    self.ranges.truncate (new_len);

    debug_assert!(self.is_valid());
    Some (isect)
  }

  /// Iterate over elements of the `RangeSet`.
  ///
  /// To iterate over individual ranges, use `range_set.as_ref().iter()`
  /// instead.
  /// 
  /// ```
  /// # use range_set::range_set;
  /// 
  /// let mut test_set = range_set![3u32..=6, 9, 22..=25];
  /// let elements: Vec<_> = test_set.iter().collect();
  /// assert_eq!(elements, vec![3, 4, 5, 6, 9, 22, 23, 24, 25]);
  /// let ranges: Vec<_> = test_set.as_ref().iter().map(|r| r.clone()).collect();
  /// assert_eq!(ranges, vec![3..=6, 9..=9, 22..=25]);
  /// 
  /// test_set.insert_range(7..=10);
  /// let elements: Vec<_> = test_set.iter().collect();
  /// assert_eq!(elements, vec![3u32, 4, 5, 6, 7, 8, 9, 10, 22, 23, 24, 25]);
  /// let ranges: Vec<_> = test_set.as_ref().iter().map(|r| r.clone()).collect();
  /// assert_eq!(ranges, vec![3u32..=10, 22..=25]);
  /// 
  /// ```
  pub fn iter (&self) -> Iter <A, T> {
    Iter {
      range_set:   self,
      range_index: 0,
      range:       T::one()..=T::zero()
    }
  }

  /// Calls `spilled` on the underlying smallvec. See [`smallvec::SmallVec::spilled`].
  /// 
  /// ```
  /// # use range_set::range_set;
  /// 
  /// let mut s = range_set![0..=2; 1];
  /// assert!(!s.spilled());
  ///
  /// assert_eq!(s.insert_range (8..=10), None);
  /// assert_eq!(s, range_set![0..=2, 8..=10]);
  /// assert!(s.spilled());
  ///
  /// assert_eq!(s.insert_range (3..=12), Some (range_set![8..=10; 1]));
  /// assert_eq!(s, range_set![0..=12]);
  /// assert!(s.spilled());  // once spilled, stays spilled
  /// 
  /// s.shrink_to_fit();  // manually un-spill
  /// assert_eq!(s, range_set![0..=12]);
  /// assert!(!s.spilled());
  /// ```
  #[inline]
  pub fn spilled (&self) -> bool {
    self.ranges.spilled()
  }

  /// Calls `shrink_to_fit` on the underlying smallvec. See [`smallvec::SmallVec::shrink_to_fit`].
  /// 
  /// ```
  /// # use range_set::range_set;
  /// 
  /// let mut s = range_set![0..=2; 1];
  /// assert!(!s.spilled());
  ///
  /// assert_eq!(s.insert_range (8..=10), None);
  /// assert_eq!(s, range_set![0..=2, 8..=10]);
  /// assert!(s.spilled());
  ///
  /// assert_eq!(s.insert_range (3..=12), Some (range_set![8..=10; 1]));
  /// assert_eq!(s, range_set![0..=12]);
  /// assert!(s.spilled());  // once spilled, stays spilled
  /// 
  /// s.shrink_to_fit();  // manually un-spill
  /// assert_eq!(s, range_set![0..=12]);
  /// assert!(!s.spilled());
  /// ```
  #[inline]
  pub fn shrink_to_fit (&mut self) {
    self.ranges.shrink_to_fit()
  }

  /// Insert helper function: search for the last range in self that is
  /// `LessThanAdjacent` or `LessThanProper` when compared with the given range
  fn binary_search_before (&self, range : &A::Item) -> Option <usize> {
    let mut before = 0;
    let mut after  = self.ranges.len();
    let mut found  = false;
    while before != after {
      let i = before + (after - before) / 2;
      let last = before;
      if self.ranges[i].end() < range.start() {
        found  = true;
        before = i;
        if before == last {
          break
        }
      } else {
        after = i
      }
    }
    if found {
      Some (before)
    } else {
      None
    }
  }

  /// Insert helper function: search for the first range in self that is
  /// `GreaterThanAdjacent` or `GreaterThanProper` when compared with the given
  /// range
  fn binary_search_after (&self, range : &A::Item) -> Option <usize> {
    let mut before = 0;
    let mut after  = self.ranges.len();
    let mut found  = false;
    while before != after {
      let i    = before + (after - before) / 2;
      let last = before;
      if range.end() < self.ranges[i].start() {
        found = true;
        after = i;
      } else {
        before = i;
        if before == last {
          break
        }
      }
    }
    if found {
      Some (after)
    } else {
      None
    }
  }

  /// Insert helper function: search for the last range in self that is
  /// `LessThanProper` when compared with the given range
  fn binary_search_before_proper (&self, range : &A::Item) -> Option <usize> {
    let mut before = 0;
    let mut after  = self.ranges.len();
    let mut found  = false;
    while before != after {
      let i = before + (after - before) / 2;
      let last = before;
      if *self.ranges[i].end()+T::one() < *range.start() {
        found  = true;
        before = i;
        if before == last {
          break
        }
      } else {
        after = i
      }
    }
    if found {
      Some (before)
    } else {
      None
    }
  }

  /// Insert helper function: search for the first range in self that is
  /// `GreaterThanProper` when compared with the given range
  fn binary_search_after_proper (&self, range : &A::Item) -> Option <usize> {
    let mut before = 0;
    let mut after  = self.ranges.len();
    let mut found  = false;
    while before != after {
      let i    = before + (after - before) / 2;
      let last = before;
      if *range.end()+T::one() < *self.ranges[i].start() {
        found = true;
        after = i;
      } else {
        before = i;
        if before == last {
          break
        }
      }
    }
    if found {
      Some (after)
    } else {
      None
    }
  }

  /// See documentation for `contains_range`. By-reference version needed for
  /// `is_subset`
  fn contains_range_ref (&self, range : &A::Item) -> bool {
    if range.is_empty() {
      return true;
    }
    if self.ranges.is_empty() {
      return false;
    }
    // Look for any the highest range completely before the requested elements.
    let test_range = if let Some(before) = self.binary_search_before(&range) {
      // The very next range must either overlap with the requested elements, or must
      // be greater than all requested elements.
      if let Some(next) = self.ranges.get(before + 1) {
        next
      } else {
        // There are no other ranges to check.
        return false;
      }
    } else {
      // There are no ranges completely before the requested elements, so try the first
      // range. This index operation cannot fail, because we checked self.ranges.is_empty()
      // above.
      &self.ranges[0]
    };
    // Check if that range contains all the requested elements.
    test_range.contains(range.start()) && test_range.contains(range.end())
  }

  /// Return the intersection of a given range with the given range of ranges in
  /// self
  fn range_intersection (&self,
    range : &A::Item, range_range : std::ops::Range <usize>
  ) -> Self {
    let mut isect = RangeSet::new();
    for i in range_range {
      let r     = &self.ranges[i];
      let rsect = intersection (&range, &r);
      if !rsect.is_empty() {
        isect.ranges.push (rsect);
      }
    }
    debug_assert!(isect.is_valid());
    isect
  }

  /// Internal validity check: all ranges are non-empty, disjoint proper with
  /// respect to one another, and sorted.
  ///
  /// Invalid range sets should be impossible to create so this function is not
  /// exposed to the user.
  #[inline]
  fn is_valid (&self) -> bool {
    valid_range_slice (&self.ranges)
  }
}

impl <A, T> From <RangeInclusive <T>> for RangeSet <A> where
  A : smallvec::Array <Item=RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug
{
  fn from (range : RangeInclusive <T>) -> Self {
    let ranges = {
      let mut v = SmallVec::new();
      v.push (range);
      v
    };
    RangeSet { ranges }
  }
}

impl <A, T> AsRef <SmallVec <A>> for RangeSet <A> where
  A : smallvec::Array <Item=RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug
{
  fn as_ref (&self) -> &SmallVec <A> {
    &self.ranges
  }
}

impl<A, B> PartialEq<RangeSet<B>> for RangeSet<A> where
  A       : smallvec::Array + Eq + std::fmt::Debug,
  A::Item : Clone + Eq + std::fmt::Debug,
  B       : smallvec::Array<Item = A::Item> + Eq + std::fmt::Debug
{
  fn eq(&self, other : &RangeSet<B>) -> bool {
    self.ranges.eq(&other.ranges)
  }
}

impl <'a, A, T> Iterator for Iter <'a, A, T> where
  A : smallvec::Array <Item=RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug,
  RangeInclusive <T> : Clone + Iterator <Item=T>
{
  type Item = T;
  fn next (&mut self) -> Option <Self::Item> {
    if let Some (t) = self.range.next() {
      Some (t)
    } else {
      if self.range_index < self.range_set.ranges.len() {
        self.range = self.range_set.ranges[self.range_index].clone();
        debug_assert!(!self.range.is_empty());
        self.range_index += 1;
        self.range.next()
      } else {
        None
      }
    }
  }
}

#[cfg(feature = "derive_serdes")]
impl<A, T> serde::Serialize for RangeSet<A> where
  A : smallvec::Array <Item=RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug + serde::Serialize,
{
  fn serialize<S: serde::Serializer>(&self, serializer: S)
    -> Result<S::Ok, S::Error>
  {
    self.ranges.serialize(serializer)
  }
}

#[cfg(feature = "derive_serdes")]
impl<'de, A, T> serde::Deserialize<'de> for RangeSet<A> where
  A : smallvec::Array <Item=RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : PrimInt + std::fmt::Debug + serde::Deserialize<'de>,
{
  fn deserialize<D: serde::Deserializer<'de>>(deserializer: D)
    -> Result<Self, D::Error>
  {
    let ranges = SmallVec::deserialize(deserializer)?;

    Ok(Self {
      ranges
    })
  }
}

////////////////////////////////////////////////////////////////////////////////
//  macros                                                                    //
////////////////////////////////////////////////////////////////////////////////

/// The default size of the inner smallvec's on-stack array.
pub const DEFAULT_RANGE_COUNT: usize = 4;

/// Convenient macro to construct RangeSets without needing bulky notation like
/// `::<[RangeInclusive<_>; _]>`.  The macro allows a mix of numbers and
/// inclusive ranges, with an optional length at the end for the smallvec array
/// size. If the length is not specified, it will default to 4.
///
/// The implementation guarantees `O(n)` construction time for lists of
/// non-adjacent mix of increasing-ranges and numbers in increasing order. See
/// [`RangeSet::from_ranges`] for more information about this
/// optimization.  Single numbers are transformed into one-element inclusive
/// ranges (`5` becomes `5..=5`).
///
/// Separately, the implementation guarantees `O(n)` construction time for lists
/// of numbers (not ranges) sorted in increasing order and deduplicated. See
/// `[RangeSet::from_elements`] for more information about this optimization.
///
/// All other cases are reasonably performant, `O(n * log(n))` on average.
/// ```
/// # use range_set::{RangeSet, range_set};
/// # use std::ops::RangeInclusive;
///
/// let case1 = RangeSet::<[RangeInclusive<u32>; 3]>::from_valid_ranges ([0..=0, 2..=5]).unwrap();
/// let case2 = RangeSet::<[RangeInclusive<u32>; 4]>::from_valid_ranges ([1..=3, 6..=15, 40..=40, 42..=50]).unwrap();
/// const FIVE: u32 = 5;
/// let some_func = |x: u32| x;
/// let your_var = 0;
///
/// // The fastest format to use is non-adjacent, increasing ranges in increasing order.
/// assert_eq!(range_set![0, 2..=5; 3], case1);
/// assert_eq!(range_set![1..=3, 6..=15, 40, 42..=50; 4], case2);
///
/// // The smallvec size is optional, and defaults to 4.
/// assert_eq!(range_set![1..=3, 6..=15, 40, 42..=50], case2);
///
/// // A wide variety of other formats are available. Complex epressions need to be surrounded
/// // by parentheses.
/// assert_eq!(range_set![0, 2, 3..=5; 3], case1);
/// assert_eq!(range_set![0, 2, (1 + 2), 4, FIVE; 3], case1);
/// assert_eq!(range_set![0, 2, (some_func(3)), 4, 5; 3], case1);
/// assert_eq!(range_set![your_var, 2..=(some_func(5)); 3], case1);
///
/// // Expressions that return ranges need to be marked using "as range":
/// let my_range = 2..=5;
/// assert_eq!(range_set![0, my_range as range; 3], case1);
///
/// // Empty lists are still allowed. Rust may have trouble inferring the number type/size
/// // in some situations.
/// assert_eq!(range_set![], RangeSet::<[RangeInclusive<u32>; 4]>::new());
/// assert_eq!(range_set![; 3], RangeSet::<[RangeInclusive<u32>; 3]>::new());
/// ```
#[macro_export]
macro_rules! range_set {
  // Empty cases: use `new`
  () => {
    $crate::RangeSet::<[core::ops::RangeInclusive<_>; $crate::DEFAULT_RANGE_COUNT]>::new()
  };
  ( ; $len:expr ) => {
    $crate::RangeSet::<[core::ops::RangeInclusive<_>; $len]>::new()
  };

  // Pure number case: Use the faster `from_elements` for just numbers, if possible.
  ( $( $num:tt ),+ ) => {
    $crate::range_set![ $( $num ),+ ; $crate::DEFAULT_RANGE_COUNT ]
  };
  ( $( $num:tt ),+ ; $len:expr ) => {
    $crate::RangeSet::<[core::ops::RangeInclusive<_>; $len]>::from_elements([ $( $num ),+ ])
  };

  // Mixed literal cases: We can support mixing numbers and ranges IF everything is a literal
  ( $( $start:tt $( ..= $end:tt )? $( as $range_keyword:tt )? ),+ ) => {
    $crate::range_set![ $( $start $(..= $end )? ),+ ; $crate::DEFAULT_RANGE_COUNT ]
  };
  ( $( $start:tt $( ..= $end:tt )? $( as $range_keyword:tt )? ),+ ; $len:expr ) => {
    $crate::RangeSet::<[core::ops::RangeInclusive<_>; $len]>::from_ranges([ $( $crate::__range_set_helper!($start $( ..= $end )? $( as $range_keyword )? ) ),+ ])
  };
}

/// Helper macro that resolves the ambiguity between literal numbers and literal
/// ranges.
#[macro_export]
#[doc(hidden)]
macro_rules! __range_set_helper {
  ( $num:tt ) => { { let val = $num; val ..= val } };
  ( $start:tt ..= $end:tt ) => ( $start ..= $end );
  ( $range_expr:tt as range) => ( $range_expr );
}

#[cfg(test)]
mod tests {
  use std::ops::RangeInclusive;
  use crate::RangeSet;

  #[test]
  fn merge_multiple() {
    let mut range_set: RangeSet<[RangeInclusive<u32>; 2]> = RangeSet::new();
    range_set.insert_range(3..=3);
    range_set.insert_range(5..=5);
    range_set.insert_range(7..=7);
    assert_eq!(
      range_set.insert_range(1..=9),
      {
        let mut r = RangeSet::from(3..=3);
        r.insert_range(5..=5);
        r.insert_range(7..=7);
        Some(r)
      }
    );

    assert_eq!(range_set.ranges.into_vec(), vec!(1..=9));
  }

  #[test]
  fn merge_multiple_then_gap() {
    let mut range_set: RangeSet<[RangeInclusive<u32>; 2]> = RangeSet::new();
    range_set.insert_range(3..=3);
    range_set.insert_range(5..=5);
    range_set.insert_range(9..=9);
    assert_eq!(
      range_set.insert_range(1..=7),
      {
        let mut r = RangeSet::from(3..=3);
        r.insert_range(5..=5);
        Some(r)
      }
    );

    assert_eq!(range_set.ranges.into_vec(), vec!(1..=7, 9..=9));
  }

  #[test]
  fn gap_then_merge_multiple() {
    let mut range_set: RangeSet<[RangeInclusive<u32>; 2]> = RangeSet::new();
    range_set.insert_range(1..=1);
    range_set.insert_range(5..=5);
    range_set.insert_range(7..=7);
    assert_eq!(
      range_set.insert_range(3..=9),
      {
        let mut r = RangeSet::from(5..=5);
        r.insert_range(7..=7);
        Some(r)
      }
    );

    assert_eq!(range_set.ranges.into_vec(), vec!(1..=1, 3..=9));
  }

  #[test]
  fn gap_then_merge_multiple_then_gap() {
    let mut range_set: RangeSet<[RangeInclusive<u32>; 2]> = RangeSet::new();
    range_set.insert_range(1..=1);
    range_set.insert_range(3..=3);
    range_set.insert_range(5..=5);
    range_set.insert_range(7..=7);
    range_set.insert_range(9..=9);
    assert_eq!(
      range_set.insert_range(3..=7),
      {
        let mut r = RangeSet::from(3..=3);
        r.insert_range(5..=5);
        r.insert_range(7..=7);
        Some(r)
      }
    );

    assert_eq!(range_set.ranges.into_vec(), vec!(1..=1, 3..=7, 9..=9));
  }

  #[test]
  fn test_range_set_macro_empty() {
    assert_eq!(range_set![; 3], RangeSet::<[RangeInclusive<u8>; 3]>::new());
    assert_eq!(range_set![], RangeSet::<[RangeInclusive<u8>; 4]>::new());
  }

  // This allow is needed due to a rust linting bug: https://github.com/rust-lang/rust/issues/113563
  #[allow(unused_parens)]
  #[test]
  fn test_range_set_macro_nums() {
    let case1 = RangeSet::<[RangeInclusive<u8>; 3]>::from_valid_ranges (
      [0..=0, 2..=5]
    ).unwrap();
    let case2 = RangeSet::<[RangeInclusive<u8>; 4]>::from_valid_ranges (
      [1..=3, 6..=6, 8..=10]
    ).unwrap();
    const SOME_CONST: u8 = 5;
    let not_token_tree = |x: u8| x;

    // All values
    assert_eq!(range_set![0, 2, 3, 4, 5; 3], case1);
    assert_eq!(range_set![0, 2, (1 + 2), 4, SOME_CONST; 3], case1);
    assert_eq!(range_set![0, 2, (not_token_tree(3)), 4, 5; 3], case1);

    assert_eq!(range_set![1, 2, 3, 6, 8, 9, 10; 4], case2);
    assert_eq!(range_set![1, 2, 3, (3 * 2), 8, 9, 10], case2);

    let mut counter = 0;
    let mut call_only_once = |x: u8| { counter += 1; x };
    assert_eq!(range_set![0, 2, (call_only_once(3)), 4, 5; 3], case1);
    assert_eq!(counter, 1);
  }

  // This allow is needed due to a rust linting bug: https://github.com/rust-lang/rust/issues/113563
  #[allow(unused_parens)]
  #[test]
  fn test_range_set_macro_mixed() {
    let case1 = RangeSet::<[RangeInclusive<u8>; 3]>::from_valid_ranges (
      [0..=0, 2..=5]
    ).unwrap();
    let case2 = RangeSet::<[RangeInclusive<u8>; 4]>::from_valid_ranges (
      [1..=3, 6..=15, 40..=40, 42..=50]
    ).unwrap();
    const SOME_CONST: u8 = 40;
    let not_token_tree = |x: u8| x;

    assert_eq!(range_set![0, 2..=5; 3], case1);
    assert_eq!(range_set![0, (not_token_tree(2))..=5; 3], case1);

    assert_eq!(range_set![1..=3, 6..=15, 40, 42..=50; 4], case2);
    assert_eq!(range_set![1, 2, 3, 6..=15, 40, 42..=50], case2);
    assert_eq!(range_set![1..=3, (3+3)..=15, SOME_CONST, 42..=50; 4], case2);
    assert_eq!(range_set![1..=3, 6..=15, 40..=40, (not_token_tree(42))..=50; 4], case2);

    let mut counter = 0;
    let mut call_only_once = |x: u8| { counter += 1; x };
    assert_eq!(range_set![1..=3, 6..=15, (call_only_once(40)), 42..=50; 4], case2);
    assert_eq!(counter, 1);

    assert_eq!(range_set![0, 2, 3, 5; 8],
      RangeSet::<[RangeInclusive<u8>; 8]>::from_valid_ranges (
        [0..=0, 2..=3, 5..=5]
      ).unwrap());
    assert_eq!(range_set![0..=0, 2..=2, (not_token_tree(4) + 1)..=5],
      RangeSet::<[RangeInclusive<u8>; 4]>::from_valid_ranges (
        [0..=0, 2..=2, 5..=5]
      ).unwrap());
  }

  #[test]
  fn test_max() {
    let mut set = RangeSet::<[RangeInclusive <u32>; 2]>::new();
    assert_eq!(set.max(), None);

    set.insert_range(4..=5);
    assert_eq!(set.max(), Some(5));

    set.insert(21);
    assert_eq!(set.max(), Some(21));

    set.insert_range(6..=13);
    assert_eq!(set.max(), Some(21));

    set.remove(21);
    assert_eq!(set.max(), Some(13));
  }

  #[test]
  fn test_min() {
    let mut set = RangeSet::<[RangeInclusive <u32>; 2]>::new();
    assert_eq!(set.min(), None);

    set.insert_range(4..=5);
    assert_eq!(set.min(), Some(4));

    set.insert(2);
    assert_eq!(set.min(), Some(2));

    set.insert_range(6..=13);
    assert_eq!(set.min(), Some(2));

    set.remove_range(2..=4);
    assert_eq!(set.min(), Some(5));
  }
}
