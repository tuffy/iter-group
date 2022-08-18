// Copyright 2022 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Extends iterators for grouping their values into a mapping type
//! whose values are a collection.
//!
//! ## Example 1
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoGroup;
//!
//! let v = vec![(1, 'a'), (2, 'b'), (3, 'c'), (2, 'd'), (1, 'e'), (1, 'f')];
//!
//! let h = v.iter().cloned().group::<HashMap<_, Vec<_>>>();
//! assert_eq!(h.get(&1), Some(&vec!['a', 'e', 'f']));
//! assert_eq!(h.get(&2), Some(&vec!['b', 'd']));
//! assert_eq!(h.get(&3), Some(&vec!['c']));
//!
//! let b = v.iter().cloned().group::<BTreeMap<_, Vec<_>>>();
//! assert_eq!(b.get(&1), Some(&vec!['a', 'e', 'f']));
//! assert_eq!(b.get(&2), Some(&vec!['b', 'd']));
//! assert_eq!(b.get(&3), Some(&vec!['c']));
//! ```
//!
//! ## Example 2
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoGroup;
//!
//! let v = vec![Some((1, 'a')), Some((2, 'b')), Some((1, 'c'))];
//!
//! let h = v.iter().cloned().group::<Option<HashMap<_, Vec<_>>>>().unwrap();
//! assert_eq!(h.get(&1), Some(&vec!['a', 'c']));
//! assert_eq!(h.get(&2), Some(&vec!['b']));
//!
//! let b = v.iter().cloned().group::<Option<BTreeMap<_, Vec<_>>>>().unwrap();
//! assert_eq!(b.get(&1), Some(&vec!['a', 'c']));
//! assert_eq!(b.get(&2), Some(&vec!['b']));
//!
//! let v = vec![Some((1, 'a')), None, Some((2, 'b'))];
//! assert!(v.iter().cloned().group::<Option<HashMap<_, Vec<_>>>>().is_none());
//! assert!(v.iter().cloned().group::<Option<BTreeMap<_, Vec<_>>>>().is_none());
//! ```
//!
//! ## Example 3
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoGroup;
//!
//! let v = vec![Ok((1, 'a')), Ok((2, 'b')), Ok((1, 'c'))];
//!
//! let h = v.iter().cloned().group::<Result<HashMap<_, Vec<_>>, ()>>().unwrap();
//! assert_eq!(h.get(&1), Some(&vec!['a', 'c']));
//! assert_eq!(h.get(&2), Some(&vec!['b']));
//!
//! let b = v.iter().cloned().group::<Result<BTreeMap<_, Vec<_>>, ()>>().unwrap();
//! assert_eq!(b.get(&1), Some(&vec!['a', 'c']));
//! assert_eq!(b.get(&2), Some(&vec!['b']));
//!
//! let v = vec![Ok((1, 'a')), Err(()), Ok((2, 'b'))];
//! assert!(v.iter().cloned().group::<Result<HashMap<_, Vec<_>>, ()>>().is_err());
//! assert!(v.iter().cloned().group::<Result<BTreeMap<_, Vec<_>>, ()>>().is_err());
//! ```

#![warn(missing_docs)]
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashMap};
use std::hash::{BuildHasher, Hash};

/// Implemented by mapping types (`HashMap` and `BTreeMap`)
/// such that they can populated by an iterator.
/// Roughly analogous to the `FromIterator` trait.
pub trait GroupFromIterator<V> {
    /// Builds a grouped collection from an iterator of key,value tuples.
    /// Collections are extended in the order the values appear
    /// in the iterator.
    ///
    /// It's recommended to call an iterator's `group()` method
    /// rather than call this directly.
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = V>;
}

#[derive(Debug)]
enum Never {}

impl<K, V, C, H> GroupFromIterator<(K, V)> for HashMap<K, C, H>
where
    K: Eq + Hash,
    C: Default + Extend<V>,
    H: BuildHasher + Default,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let r: Result<Self, Never> = GroupFromIterator::group_from_iter(iter.into_iter().map(Ok));
        r.unwrap()
    }
}

impl<K, V, C, H> GroupFromIterator<Option<(K, V)>> for Option<HashMap<K, C, H>>
where
    K: Eq + Hash,
    C: Default + Extend<V>,
    H: BuildHasher + Default,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Option<(K, V)>>,
    {
        let r: Result<HashMap<K, C, H>, ()> = GroupFromIterator::group_from_iter(iter.into_iter().map(|o| o.ok_or(())));
        r.ok()
    }
}

impl<K, V, C, E, H> GroupFromIterator<Result<(K, V), E>> for Result<HashMap<K, C, H>, E>
where
    K: Eq + Hash,
    C: Default + Extend<V>,
    H: BuildHasher + Default,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Result<(K, V), E>>,
    {
        let mut h: HashMap<K, C, H> = HashMap::default();

        for r in iter {
            let (k, v) = r?;
            h.entry(k).or_default().extend(std::iter::once(v));
        }

        Ok(h)
    }
}

impl<K, V, C> GroupFromIterator<(K, V)> for BTreeMap<K, C>
where
    K: Ord,
    C: Default + Extend<V>,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let r: Result<Self, Never> = GroupFromIterator::group_from_iter(iter.into_iter().map(Ok));
        r.unwrap()
    }
}

impl<K, V, C> GroupFromIterator<Option<(K, V)>> for Option<BTreeMap<K, C>>
where
    K: Ord,
    C: Default + Extend<V>,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Option<(K, V)>>,
    {
        let r: Result<BTreeMap<K, C>, ()> = GroupFromIterator::group_from_iter(iter.into_iter().map(|o| o.ok_or(())));
        r.ok()
    }
}

impl<K, V, C, E> GroupFromIterator<Result<(K, V), E>> for Result<BTreeMap<K, C>, E>
where
    K: Ord,
    C: Default + Extend<V>,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Result<(K, V), E>>,
    {
        let mut b: BTreeMap<K, C> = BTreeMap::default();

        for r in iter {
            let (k, v) = r?;
            b.entry(k).or_default().extend(std::iter::once(v));
        }

        Ok(b)
    }
}

/// Extends Iterators with an additional grouping method.
pub trait IntoGroup<V> {
    /// Consumes the iterator and returns a grouping of its contents.
    fn group<B: GroupFromIterator<V>>(self) -> B;
}

impl<V, I> IntoGroup<V> for I
where
    I: Iterator<Item = V>,
{
    #[inline]
    fn group<B: GroupFromIterator<V>>(self) -> B {
        B::group_from_iter(self)
    }
}
