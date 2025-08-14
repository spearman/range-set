//! Type and functions for comparing inclusive ranges

use std;
use num_traits::PrimInt;

////////////////////////////////////////////////////////////////////////////////
//  enums                                                                     //
////////////////////////////////////////////////////////////////////////////////

/// Result of comparing a pair of ranges `(A,B)`
#[derive(Debug,Eq,PartialEq)]
pub enum RangeCompare {
  Disjoint  (RangeDisjoint),
  Intersect (RangeIntersect)
}

/// Ways in which a pair of ranges `(A,B)` can be disjoint
#[derive(Debug,Eq,PartialEq)]
pub enum RangeDisjoint {
  /// `A = B = {}`
  EmptyBoth,
  /// `A = {}`
  EmptyLhs,
  /// `B = {}`
  EmptyRhs,
  /// `[ A ]  [ B ]`
  LessThanProper,
  /// `[ A ][ B ]`
  LessThanAdjacent,
  /// `[ B ]  [ A ]`
  GreaterThanProper,
  /// `[ B ][ A ]`
  GreaterThanAdjacent
}

/// Ways in which a pair of ranges `(A,B)` can intersect
#[derive(Debug,Eq,PartialEq)]
pub enum RangeIntersect {
  /// `[ A=B ]`
  EqualTo,
  /// `[ A [ ] B ]`
  OverlapsLeft,
  /// `[ B [ ] A ]`
  OverlapsRight,
  /// `[ B ] A ]`
  ContainsFirst,
  /// `[ A [ B ] ]`
  ContainsProper,
  /// `[ A [ B ]`
  ContainsLast,
  /// `[ A ] B ]`
  ContainedByFirst,
  /// `[ [ A ] B ]`
  ContainedByProper,
  /// `[ B [ A ]`
  ContainedByLast
}

////////////////////////////////////////////////////////////////////////////////
//  functions                                                                 //
////////////////////////////////////////////////////////////////////////////////

/// Compare two inclusive ranges.
///
/// ```
/// # use range_set::*;
/// assert_eq!(
///   range_compare (&(0..=5), &(0..=5)),
///   RangeCompare::Intersect (RangeIntersect::EqualTo));
/// assert_eq!(
///   range_compare (&(1..=0), &(1..=0)),
///   RangeCompare::Disjoint (RangeDisjoint::EmptyBoth));
/// ```
pub fn range_compare <T : PrimInt> (
  left : &std::ops::RangeInclusive <T>, right : &std::ops::RangeInclusive <T>
) -> RangeCompare {
  if let Some (disjoint) = RangeDisjoint::compare (left, right) {
    disjoint.into()
  } else if let Some (intersect) = RangeIntersect::compare (left, right) {
    intersect.into()
  } else {
    unreachable!()
  }
}

/// Compute the intersection of two inclusive ranges. Returns an empty range
/// if they are disjoint.
///
/// ```
/// # use range_set::*;
/// assert_eq!(intersection (&(0..=3), &(2..=5)), 2..=3);
/// assert!(intersection (&(0..=2), &(3..=5)).is_empty());
/// ```
pub fn intersection <T : PrimInt> (
  left : &std::ops::RangeInclusive <T>, right : &std::ops::RangeInclusive <T>
) -> std::ops::RangeInclusive <T> {
  if RangeDisjoint::compare (left, right).is_none() {
    std::cmp::max (*left.start(), *right.start())..=
    std::cmp::min (*left.end(), *right.end())
  } else {
    T::one()..=T::zero()
  }
}

////////////////////////////////////////////////////////////////////////////////
//  impls                                                                     //
////////////////////////////////////////////////////////////////////////////////

impl From <RangeDisjoint> for RangeCompare {
  fn from (disjoint : RangeDisjoint) -> Self {
    RangeCompare::Disjoint (disjoint)
  }
}

impl From <RangeIntersect> for RangeCompare {
  fn from (intersect : RangeIntersect) -> Self {
    RangeCompare::Intersect (intersect)
  }
}

impl RangeDisjoint {
  /// Tests two inclusive ranges for disjointness, returning `None` if they
  /// intersect.
  ///
  /// ```
  /// # use range_set::*;
  /// assert_eq!(RangeDisjoint::compare (&(0..=5), &(0..=5)), None);
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(1..=0), &(1..=0)),
  ///   Some (RangeDisjoint::EmptyBoth));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(1..=0), &(0..=5)),
  ///   Some (RangeDisjoint::EmptyLhs));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(0..=5), &(1..=0)),
  ///   Some (RangeDisjoint::EmptyRhs));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(0..=2), &(4..=5)),
  ///   Some (RangeDisjoint::LessThanProper));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(0..=2), &(3..=5)),
  ///   Some (RangeDisjoint::LessThanAdjacent));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(4..=5), &(0..=2)),
  ///   Some (RangeDisjoint::GreaterThanProper));
  /// assert_eq!(
  ///   RangeDisjoint::compare (&(3..=5), &(0..=2)),
  ///   Some (RangeDisjoint::GreaterThanAdjacent));
  /// ```
  pub fn compare <T : PrimInt> (
    left : &std::ops::RangeInclusive <T>, right : &std::ops::RangeInclusive <T>
  ) -> Option <Self> {
    match (left.is_empty(), right.is_empty()) {
      (true, true)   => Some (RangeDisjoint::EmptyBoth),
      (true, false)  => Some (RangeDisjoint::EmptyLhs),
      (false, true)  => Some (RangeDisjoint::EmptyRhs),
      (false, false) => if right.start() <= left.end()
        && left.start() <= right.end()
        || left.start() <= right.end() && right.start() <= left.end()
      {
        None  // intersection
      } else {
        Some (
          if left.end() < right.start() {
            match *right.start() - *left.end() {
              x if x == T::one() => RangeDisjoint::LessThanAdjacent,
              _                  => RangeDisjoint::LessThanProper
            }
          } else {
            debug_assert!(right.end() < left.start());
            match *left.start() - *right.end() {
              x if x == T::one() => RangeDisjoint::GreaterThanAdjacent,
              _                  => RangeDisjoint::GreaterThanProper
            }
          }
        )
      }
    }
  }
}

impl RangeIntersect {
  /// Test two inclusive ranges for intersection, returning `None` if the
  /// ranges are disjoint.
  ///
  /// ```
  /// # use range_set::*;
  /// assert_eq!(RangeIntersect::compare (&(0..=1), &(4..=5)), None);
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=5), &(0..=5)),
  ///   Some (RangeIntersect::EqualTo));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=5), &(1..=4)),
  ///   Some (RangeIntersect::ContainsProper));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(1..=4), &(0..=5)),
  ///   Some (RangeIntersect::ContainedByProper));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=5), &(0..=3)),
  ///   Some (RangeIntersect::ContainsFirst));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=5), &(4..=5)),
  ///   Some (RangeIntersect::ContainsLast));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=2), &(0..=5)),
  ///   Some (RangeIntersect::ContainedByFirst));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(4..=5), &(0..=5)),
  ///   Some (RangeIntersect::ContainedByLast));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(0..=3), &(3..=5)),
  ///   Some (RangeIntersect::OverlapsLeft));
  /// assert_eq!(
  ///   RangeIntersect::compare (&(3..=5), &(0..=3)),
  ///   Some (RangeIntersect::OverlapsRight));
  /// ```
  pub fn compare <T : PrimInt> (
    left : &std::ops::RangeInclusive <T>, right : &std::ops::RangeInclusive <T>
  ) -> Option <Self> {
    match (left.is_empty(), right.is_empty()) {
      (true, true) | (true, false) | (false, true) => None,
      (false, false) => if left.end() < right.start() ||
        right.end() < left.start()
      {
        None  // disjoint
      } else {
        Some (if left == right {
          RangeIntersect::EqualTo
        } else {
          match left.start().cmp (right.start()) {
            std::cmp::Ordering::Less => match left.end().cmp (right.end()) {
              std::cmp::Ordering::Less    => RangeIntersect::OverlapsLeft,
              std::cmp::Ordering::Equal   => RangeIntersect::ContainsLast,
              std::cmp::Ordering::Greater => RangeIntersect::ContainsProper
            }
            std::cmp::Ordering::Equal => match left.end().cmp (right.end()) {
              std::cmp::Ordering::Less    => RangeIntersect::ContainedByFirst,
              std::cmp::Ordering::Equal   => unreachable!(),
              std::cmp::Ordering::Greater => RangeIntersect::ContainsFirst
            }
            std::cmp::Ordering::Greater => match left.end().cmp (right.end()) {
              std::cmp::Ordering::Less    => RangeIntersect::ContainedByProper,
              std::cmp::Ordering::Equal   => RangeIntersect::ContainedByLast,
              std::cmp::Ordering::Greater => RangeIntersect::OverlapsRight
            }
          }
        })
      }
    }
  }
}
