//! `RangeSet` container type.
//!
//! `RangeSet` stores collections of `PrimInt` values as inclusive ranges using
//! generic [`SmallVec`](https://docs.rs/smallvec)-backed storage. This means
//! that a certain amount of ranges will fit on the stack before spilling over
//! to the heap.

extern crate num_traits;
#[cfg(feature = "serde")]
extern crate serde_crate as serde;
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
/// # extern crate smallvec;
/// # extern crate range_set;
/// # use range_set::RangeSet;
/// # use smallvec::SmallVec;
/// # use std::ops::RangeInclusive;
/// # fn main() {
/// let mut s = RangeSet::<[RangeInclusive <u32>; 1]>::from (0..=2);
/// println!("s: {:?}", s);
/// assert!(!s.spilled());
///
/// assert!(s.insert_range (8..=10).is_none());
/// println!("s: {:?}", s);
/// assert!(s.spilled());
/// let v : Vec <u32> = s.iter().collect();
/// assert_eq!(v, vec![0,1,2,8,9,10]);
///
/// assert_eq!(s.insert_range (3..=12), Some (RangeSet::from (8..=10)));
/// println!("s: {:?}", s);
/// assert!(s.spilled());  // once spilled, stays spilled
/// let v : Vec <u32> = s.iter().collect();
/// assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);
/// s.shrink_to_fit();  // manually un-spill
/// assert!(!s.spilled());
/// # }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
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
/// # extern crate smallvec;
/// # extern crate range_set;
/// # use std::ops::RangeInclusive;
/// # use range_set::*;
/// # fn main() {
/// let mut v = Vec::new();
/// assert!(valid_range_slice (&v));
/// v.push (0..=3);
/// assert!(valid_range_slice (&v));
/// v.push (6..=10);
/// assert!(valid_range_slice (&v));
/// v.push (0..=1);
/// assert!(!valid_range_slice (&v));
/// # }
/// ```
pub fn valid_range_slice <T, V> (ranges : V) -> bool where
  T : PartialOrd + PrimInt,
  V : AsRef <[RangeInclusive <T>]>
{
  let ranges = ranges.as_ref();
  if !ranges.as_ref().is_empty() {
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
  #[inline]
  pub fn new() -> Self {
    RangeSet {
      ranges: SmallVec::new()
    }
  }

  /// New empty range set with the internal smallvec initialized with the given
  /// initial capacity
  #[inline]
  pub fn with_capacity (capacity : usize) -> Self {
    RangeSet {
      ranges: SmallVec::with_capacity (capacity)
    }
  }

  /// Returns a new range set if the given slice of ranges is valid and sorted
  /// (`valid_range_slice`)
  #[inline]
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

  /// Insert a single element, returning true if it was successfully inserted
  /// or else false if it was already present
  ///
  /// ```
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::new();
  /// assert!(s.insert (4));
  /// assert_eq!(s, RangeSet::from (4..=4));
  /// assert!(!s.insert (4));
  /// assert_eq!(s, RangeSet::from (4..=4));
  /// assert!(s.insert (5));
  /// assert_eq!(s, RangeSet::from (4..=5));
  /// assert!(s.insert (3));
  /// assert_eq!(s, RangeSet::from (3..=5));
  /// assert!(s.insert (10));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([3..=5, 10..=10]).unwrap());
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
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert!(s.remove (1));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=0, 2..=5]).unwrap());
  /// assert!(!s.remove (1));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=0, 2..=5]).unwrap());
  /// assert!(s.remove (4));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=0, 2..=3, 5..=5]).unwrap());
  /// assert!(s.remove (3));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=0, 2..=2, 5..=5]).unwrap());
  /// assert!(s.remove (2));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=0, 5..=5]).unwrap());
  /// assert!(s.remove (0));
  /// assert_eq!(s, RangeSet::from (5..=5));
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
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.insert_range ( 3..=10), Some (RangeSet::from (3..=5)));
  /// assert_eq!(s.insert_range (20..=30), None);
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

  /// Removes and returns the intersected elements, if there were any.
  ///
  /// ```
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.remove_range (3..=3), Some (RangeSet::from (3..=3)));
  /// assert_eq!(s, RangeSet::from_valid_ranges ([0..=2, 4..=5]).unwrap());
  /// assert_eq!(s.remove_range (0..=10), Some (
  ///   RangeSet::from_valid_ranges ([0..=2, 4..=5]).unwrap()));
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
  pub fn iter (&self) -> Iter <A, T> {
    Iter {
      range_set:   self,
      range_index: 0,
      range:       T::one()..=T::zero()
    }
  }

  /// Calls `spilled` on the underlying smallvec
  #[inline]
  pub fn spilled (&self) -> bool {
    self.ranges.spilled()
  }

  /// Calls `shrink_to_fit` on the underlying smallvec
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

#[cfg(feature = "serde")]
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

#[cfg(feature = "serde")]
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
}
