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

/// A set of elements represented as a sorted list of inclusive ranges.
///
/// ```
/// # #![feature(inclusive_range_syntax)]
/// # use range_set::RangeSet;
/// let mut s = RangeSet::<u8>::from (0..=3);
/// assert!(s.insert_range (7..=10).is_none());
/// let mut v = Vec::new();
/// for b in s.iter() {
///   v.push (b);
/// }
/// assert_eq!(v, vec![0,1,2,3,7,8,9,10]);
/// assert!(s.insert_range (4..=6).is_none());
/// v.clear();
/// for b in s.iter() {
///   v.push (b);
/// }
/// assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10]);
/// assert_eq!(
///   s.insert_range (7..=12),
///   Some (RangeSet::from (7..=10)));
/// v.clear();
/// for b in s.iter() {
///   v.push (b);
/// }
/// assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12]);
/// ```
#[derive(Debug,Eq,PartialEq)]
pub struct RangeSet <T : num::PrimInt> {
  ranges : smallvec::SmallVec <[std::ops::RangeInclusive <T>; 1]>
}

pub struct Iter <'a, T : 'a + num::PrimInt> {
  range_set:   &'a RangeSet <T>,
  range_index: usize,
  range:       std::ops::RangeInclusive <T>
}

///////////////////////////////////////////////////////////////////////////////
//  functions                                                                //
///////////////////////////////////////////////////////////////////////////////

/// Tests a raw smallvec of ranges for validity as a range set: the element
/// ranges must be properly disjoint (not adjacent) and sorted.
///
/// ```
/// # #![feature(inclusive_range_syntax)]
/// # extern crate smallvec;
/// # extern crate range_set;
/// # use smallvec::SmallVec;
/// # use range_set::*;
/// # fn main() {
/// let mut v = SmallVec::new();
/// assert!(valid_range_vec (&v));
/// v.push (0..=3);
/// assert!(valid_range_vec (&v));
/// v.push (6..=10);
/// assert!(valid_range_vec (&v));
/// v.push (0..=1);
/// assert!(!valid_range_vec (&v));
/// # }
/// ```
pub fn valid_range_vec <T : num::PrimInt>
  (ranges : &smallvec::SmallVec <[std::ops::RangeInclusive <T>; 1]>) -> bool
{
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

///////////////////////////////////////////////////////////////////////////////
//  impls                                                                    //
///////////////////////////////////////////////////////////////////////////////

impl <T : num::PrimInt + std::fmt::Debug> RangeSet <T> {
  /// New empty range set
  #[inline]
  pub fn new() -> Self {
    RangeSet {
      ranges: smallvec::SmallVec::new()
    }
  }

  /// Returns a new range set if the given vector of ranges is valid
  /// (`valid_range_vec`)
  #[inline]
  pub fn from_ranges (
    ranges : smallvec::SmallVec <[std::ops::RangeInclusive <T>; 1]>
  ) -> Option <Self> {
    if valid_range_vec (&ranges) {
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

  /// Returns the intersected values if the range is not disjoint
  /// with the curret range set.
  ///
  /// ```
  /// # #![feature(inclusive_range_syntax)]
  /// # use range_set::RangeSet;
  /// let mut s = RangeSet::<u8>::from (0..=5);
  /// assert_eq!(s.insert_range ( 3..=10), Some (RangeSet::from (3..=5)));
  /// assert_eq!(s.insert_range (20..=30), None);
  /// ```
  pub fn insert_range (&mut self, range : std::ops::RangeInclusive <T>)
    -> Option <Self>
  {
    if is_empty (&range) {       // empty range
      return None
    }
    if self.ranges.is_empty() { // empty range set
      self.ranges.push (range);
      return None
    }
    let before = Self::binary_search_before (self, &range);
    let after  = Self::binary_search_after  (self, &range);
    match (before, after) {
      // no existing ranges are properly greater than or less than the range:
      // this means that both the first range and the last range are either
      // intersected with or adjacent to the given range, implying that the
      // range set will be fused to a single range containing the min and max
      // of the intersection of the given range and the existing range set
      (None, None) => {
        let mut isect = RangeSet::new();
        for r in self.ranges.iter() {
          let rsect = intersection (&range, &r);
          if !is_empty (&rsect) {
            isect.ranges.push (rsect);
          }
          debug_assert!(isect.is_valid());
        }
        self.ranges = smallvec::SmallVec::from_buf ([
          std::cmp::min (range.start, self.ranges[0].start)..=
          std::cmp::max (range.end,   self.ranges[self.ranges.len()-1].end)
        ]);
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
          let mut isect = RangeSet::new();
          for i in before+1..self.ranges.len() {
            let r     = &self.ranges[i];
            let rsect = intersection (&range, &r);
            if !is_empty (&rsect) {
              isect.ranges.push (rsect);
            }
            debug_assert!(isect.is_valid());
          }
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
          let mut isect = RangeSet::new();
          for i in 0..after {
            let r     = &self.ranges[i];
            let rsect = intersection (&range, &r);
            if !is_empty (&rsect) {
              isect.ranges.push (rsect);
            }
            debug_assert!(isect.is_valid());
          }
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
          let mut isect = RangeSet::new();
          for i in before+1..after {
            let r     = &self.ranges[i];
            let rsect = intersection (&range, &r);
            if !is_empty (&rsect) {
              isect.ranges.push (rsect);
            }
            debug_assert!(isect.is_valid());
          }
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

  /// Returns the removed elements if they were present
  pub fn remove_range (&mut self, range : std::ops::RangeInclusive <T>)
    -> Option <Self>
  {
    unimplemented!()
  }

  pub fn iter (&self) -> Iter <T> {
    Iter {
      range_set:   self,
      range_index: 0,
      range:       T::one()..=T::zero()
    }
  }

  /// Insert helper function: search for the last range in self that is
  /// `LessThanProper` when compared with the given range
  fn binary_search_before (&self, range : &std::ops::RangeInclusive <T>)
    -> Option <usize>
  {
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
  fn binary_search_after (&self, range : &std::ops::RangeInclusive <T>)
    -> Option <usize>
  {
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

  /// Internal validity check: all ranges are non-empty, disjoint proper with
  /// respect to one another, and sorted.
  ///
  /// Invalid range sets should be impossible to create so this function is not
  /// exposed to the user.
  #[inline]
  fn is_valid (&self) -> bool {
    valid_range_vec (&self.ranges)
  }
}

impl <T : num::PrimInt> From <std::ops::RangeInclusive <T>> for RangeSet <T> {
  fn from (range : std::ops::RangeInclusive <T>) -> Self {
    RangeSet {
      ranges: smallvec::SmallVec::from ([range])
    }
  }
}

impl <'a, T : num::PrimInt> Iterator for Iter <'a, T> where
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
