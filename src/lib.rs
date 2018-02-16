#![feature(inclusive_range)]
#![feature(inclusive_range_syntax)]
#![feature(exact_size_is_empty)]

extern crate num;
extern crate smallvec;

pub mod range_compare;

pub use range_compare::{
  RangeCompare, RangeDisjoint, RangeIntersect,
  range_compare, intersection, is_empty
};

///////////////////////////////////////////////////////////////////////////////
//  structs                                                                  //
///////////////////////////////////////////////////////////////////////////////

/// A set of primitive integers represented as a sorted list of inclusive
/// ranges.
///
/// ```
/// # #![feature(inclusive_range)]
/// # #![feature(inclusive_range_syntax)]
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
#[derive(Clone,Debug,Eq,PartialEq)]
pub struct RangeSet <A> where
  A       : smallvec::Array + Eq + std::fmt::Debug,
  A::Item : Clone + Eq + std::fmt::Debug
{
  ranges  : smallvec::SmallVec <A>
}

pub struct Iter <'a, A, T> where
  A : 'a + smallvec::Array <Item=std::ops::RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : 'a + num::PrimInt + std::fmt::Debug
{
  range_set   : &'a RangeSet <A>,
  range_index : usize,
  range       : std::ops::RangeInclusive <T>
}

///////////////////////////////////////////////////////////////////////////////
//  functions                                                                //
///////////////////////////////////////////////////////////////////////////////

/// Report some sizes of various range set types
pub fn report() {
  use std::ops::RangeInclusive;

  println!("RangeSet report...");

  println!("  size of RangeSet <[RangeInclusive <u32>; 1]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 1]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u16>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 1]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 1]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u64>; 1]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 1]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <usize>; 1]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 2]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 2]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u16>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 2]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 2]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u64>; 2]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 2]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <usize>; 2]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 4]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 4]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u16>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 4]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 4]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u64>; 4]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 4]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <usize>; 4]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 8]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 8]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u16>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 8]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 8]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u64>; 8]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 8]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <usize>; 8]>>());

  println!("  size of RangeSet <[RangeInclusive <u32>; 16]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u16>; 16]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u16>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u32>; 16]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u32>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <u64>; 16]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <u64>; 16]>>());
  println!("  size of RangeSet <[RangeInclusive <usize>; 16]>: {}",
    std::mem::size_of::<RangeSet <[RangeInclusive <usize>; 16]>>());

  println!("...RangeSet report");
}

///////////////////////////////////////////////////////////////////////////////
//  impls                                                                    //
///////////////////////////////////////////////////////////////////////////////

// the majority of the logic for modifying range sets are the insert_range and
// remove_range methods
//
// there are some helper functions with additional logic such as the
// binary_search functions
impl <A, T> RangeSet <A> where
  A : smallvec::Array <Item=std::ops::RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : num::PrimInt + std::fmt::Debug
{
  /// New empty range set
  #[inline]
  pub fn new() -> Self {
    RangeSet {
      ranges: smallvec::SmallVec::new()
    }
  }

  /// New empty range set with the internal smallvec initialized with the given
  /// initial capacity
  #[inline]
  pub fn with_capacity (capacity : usize) -> Self {
    RangeSet {
      ranges: smallvec::SmallVec::with_capacity (capacity)
    }
  }

  /// Returns a new range set if the given vector of ranges is valid
  /// (`valid_range_vec`)
  #[inline]
  pub fn from_ranges (ranges : smallvec::SmallVec <A>) -> Option <Self> {
    if Self::valid_range_vec (&ranges) {
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
  pub fn into_smallvec (self) -> smallvec::SmallVec <A> {
    self.ranges
  }

  /// Insert a single element, returning true if it was successfully inserted
  /// or else false if it was already present
  ///
  /// ```
  /// # #![feature(inclusive_range)]
  /// # #![feature(inclusive_range_syntax)]
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
  /// assert_eq!(s, RangeSet::from_ranges (vec![3..=5, 10..=10].into()).unwrap());
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
  /// # #![feature(inclusive_range)]
  /// # #![feature(inclusive_range_syntax)]
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert!(s.remove (1));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=0, 2..=5].into()).unwrap());
  /// assert!(!s.remove (1));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=0, 2..=5].into()).unwrap());
  /// assert!(s.remove (4));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=0, 2..=3, 5..=5].into()).unwrap());
  /// assert!(s.remove (3));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=0, 2..=2, 5..=5].into()).unwrap());
  /// assert!(s.remove (2));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=0, 5..=5].into()).unwrap());
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
  /// # #![feature(inclusive_range)]
  /// # #![feature(inclusive_range_syntax)]
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.insert_range ( 3..=10), Some (RangeSet::from (3..=5)));
  /// assert_eq!(s.insert_range (20..=30), None);
  /// ```
  pub fn insert_range (&mut self, range : A::Item) -> Option <Self> {
    if is_empty (&range) {       // empty range
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
          std::cmp::min (range.start, self.ranges[0].start)..=
          std::cmp::max (range.end,   self.ranges[self.ranges.len()-1].end);
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
            std::cmp::min (range.start, self.ranges[before+1].start)..=
            std::cmp::max (range.end, self.ranges[self.ranges.len()-1].end);
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
            std::cmp::min (range.start, self.ranges[0].start)..=
            std::cmp::max (range.end, self.ranges[after-1].end);
          for i in 0..after {
            self.ranges[i+1] = self.ranges[after + i].clone();
          }
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
            std::cmp::min (range.start, self.ranges[before+1].start)..=
            std::cmp::max (range.end, self.ranges[after-1].end);
          // if there are more than one ranges between we must shift and truncate
          if 1 < after - before - 1 {
            for i in 0..(after-before-1) {
              self.ranges[before+1+i] = self.ranges[after + i].clone();
            }
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
  /// # #![feature(inclusive_range)]
  /// # #![feature(inclusive_range_syntax)]
  /// # use range_set::RangeSet;
  /// # use std::ops::RangeInclusive;
  /// let mut s = RangeSet::<[RangeInclusive <u32>; 2]>::from (0..=5);
  /// assert_eq!(s.remove_range (3..=3), Some (RangeSet::from (3..=3)));
  /// assert_eq!(s, RangeSet::from_ranges (vec![0..=2, 4..=5].into()).unwrap());
  /// assert_eq!(s.remove_range (0..=10), Some (
  ///   RangeSet::from_ranges (vec![0..=2, 4..=5].into()).unwrap()));
  /// assert!(s.is_empty());
  /// ```
  pub fn remove_range (&mut self, range : A::Item) -> Option <Self> {
    if self.ranges.is_empty() || is_empty (&range) {  // empty
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
      if single_range.start < range.start && range.end < single_range.end {
        let left  = single_range.start..=range.start - T::one();
        let right = range.end + T::one()..=single_range.end;
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
      range.start <= first.start && last.end <= range.end
    {
      (isect_first, isect_last)
    // first intersected range remains but is shortened
    } else if first.start < range.start && last.end <= range.end {
      self.ranges[isect_first].end = range.start - T::one();
      (isect_first+1, isect_last)
    // last intersected range remains but is shortened
    } else if range.start <= first.start && range.end < last.end {
      self.ranges[isect_last-1].start = range.end + T::one();
      (isect_first, isect_last-1)
    // both first and last range remain and are shortened
    } else {
      debug_assert!(first.start < range.start && range.end < last.end);
      self.ranges[isect_first].end    = range.start - T::one();
      self.ranges[isect_last-1].start = range.end   + T::one();
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

  pub fn iter (&self) -> Iter <A, T> {
    Iter {
      range_set:   self,
      range_index: 0,
      range:       T::one()..=T::zero()
    }
  }

  /// Tests a raw smallvec of ranges for validity as a range set: the element
  /// ranges must be properly disjoint (not adjacent) and sorted.
  ///
  /// ```
  /// # #![feature(inclusive_range)]
  /// # #![feature(inclusive_range_syntax)]
  /// # extern crate smallvec;
  /// # extern crate range_set;
  /// # use std::ops::RangeInclusive;
  /// # use smallvec::SmallVec;
  /// # use range_set::*;
  /// # fn main() {
  /// let mut v = SmallVec::<[RangeInclusive <u32>; 2]>::new();
  /// assert!(RangeSet::valid_range_vec (&v));
  /// v.push (0..=3);
  /// assert!(RangeSet::valid_range_vec (&v));
  /// v.push (6..=10);
  /// assert!(RangeSet::valid_range_vec (&v));
  /// v.push (0..=1);
  /// assert!(!RangeSet::valid_range_vec (&v));
  /// # }
  /// ```
  pub fn valid_range_vec (
    ranges : &smallvec::SmallVec <A>
  ) -> bool {
    if !ranges.is_empty() {
      for i in 0..ranges.len()-1 { // safe to subtract here since non-empty
        let this = &ranges[i];
        let next = &ranges[i+1];  // safe to index
        if is_empty (this) || is_empty (next) {
          return false
        }
        if next.start <= this.end+T::one() {
          return false
        }
      }
    }
    true
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
      if self.ranges[i].end+T::one() <= range.start {
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
      if range.end+T::one() <= self.ranges[i].start {
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
      if self.ranges[i].end+T::one() < range.start {
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
      if range.end+T::one() < self.ranges[i].start {
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
      if !is_empty (&rsect) {
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
    Self::valid_range_vec (&self.ranges)
  }
}

impl <A, T> From <std::ops::RangeInclusive <T>> for RangeSet <A> where
  A : smallvec::Array <Item=std::ops::RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : num::PrimInt + std::fmt::Debug
{
  fn from (range : std::ops::RangeInclusive <T>) -> Self {
    let ranges = {
      let mut v = smallvec::SmallVec::new();
      v.push (range);
      v
    };
    RangeSet { ranges }
  }
}

impl <'a, A, T> Iterator for Iter <'a, A, T> where
  A : smallvec::Array <Item=std::ops::RangeInclusive <T>>
    + Eq + std::fmt::Debug,
  T : num::PrimInt + std::fmt::Debug,
  std::ops::RangeInclusive <T> : Clone + Iterator <Item=T>
{
  type Item = T;
  fn next (&mut self) -> Option <Self::Item> {
    if let Some (t) = self.range.next() {
      Some (t)
    } else {
      if self.range_index < self.range_set.ranges.len() {
        self.range = self.range_set.ranges[self.range_index].clone();
        debug_assert!(!is_empty (&self.range));
        self.range_index += 1;
        self.range.next()
      } else {
        None
      }
    }
  }
}

/*
#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
      assert_eq!(2 + 2, 4);
  }
}
*/
