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
//!
//! Also offers the option to extend iterators for summarizing their values
//! into a mapping type whose values are a sum.
//!
//! # Example 1
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoSummary;
//!
//! let v = vec![('a', 1), ('b', 1), ('a', 2), ('b', 2), ('a', 3)];
//!
//! let h = v.iter().cloned().summarize::<HashMap<_, _>>();
//! assert_eq!(h.get(&'a'), Some(&6));
//! assert_eq!(h.get(&'b'), Some(&3));
//!
//! let b = v.iter().cloned().summarize::<BTreeMap<_, _>>();
//! assert_eq!(b.get(&'a'), Some(&6));
//! assert_eq!(b.get(&'b'), Some(&3));
//! ```
//!
//! ## Example 2
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoSummary;
//!
//! let v = vec![Some(('a', 1)), Some(('b', 2)), Some(('a', 3))];
//!
//! let h = v.iter().cloned().summarize::<Option<HashMap<_, _>>>().unwrap();
//! assert_eq!(h.get(&'a'), Some(&4));
//! assert_eq!(h.get(&'b'), Some(&2));
//!
//! let b = v.iter().cloned().summarize::<Option<BTreeMap<_, _>>>().unwrap();
//! assert_eq!(b.get(&'a'), Some(&4));
//! assert_eq!(b.get(&'b'), Some(&2));
//!
//! let v = vec![Some(('a', 1)), None, Some(('b', 2))];
//! assert!(v.iter().cloned().summarize::<Option<HashMap<_, _>>>().is_none());
//! assert!(v.iter().cloned().summarize::<Option<BTreeMap<_, _>>>().is_none());
//! ```
//!
//! ## Example 3
//! ```
//! use std::collections::{BTreeMap, HashMap};
//! use iter_group::IntoSummary;
//!
//! let v = vec![Ok(('a', 1)), Ok(('b', 2)), Ok(('a', 3))];
//!
//! let h = v.iter().cloned().summarize::<Result<HashMap<_, _>, ()>>().unwrap();
//! assert_eq!(h.get(&'a'), Some(&4));
//! assert_eq!(h.get(&'b'), Some(&2));
//!
//! let b = v.iter().cloned().summarize::<Result<BTreeMap<_, _>, ()>>().unwrap();
//! assert_eq!(b.get(&'a'), Some(&4));
//! assert_eq!(b.get(&'b'), Some(&2));
//!
//! let v = vec![Ok(('a', 1)), Err(()), Ok(('b', 2))];
//! assert!(v.iter().cloned().summarize::<Result<HashMap<_, _>, ()>>().is_err());
//! assert!(v.iter().cloned().summarize::<Result<BTreeMap<_, _>, ()>>().is_err());
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

impl<K, V, C> GroupFromIterator<(K, V)> for C
where
    C: InsertAndExtend<K, V>,
{
    #[inline]
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        #[derive(Debug)]
        enum Never {}

        let r: Result<Self, Never> = GroupFromIterator::group_from_iter(iter.into_iter().map(Ok));
        r.unwrap()
    }
}

impl<K, V, C> GroupFromIterator<Option<(K, V)>> for Option<C>
where
    C: InsertAndExtend<K, V>,
{
    #[inline]
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Option<(K, V)>>,
    {
        let r: Result<C, ()> =
            GroupFromIterator::group_from_iter(iter.into_iter().map(|o| o.ok_or(())));
        r.ok()
    }
}

impl<K, V, C, E> GroupFromIterator<Result<(K, V), E>> for Result<C, E>
where
    C: InsertAndExtend<K, V>,
{
    fn group_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Result<(K, V), E>>,
    {
        let mut h = C::default();

        for r in iter {
            let (k, v) = r?;
            h.insert_and_extend(k, v);
        }

        Ok(h)
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

/// A trait for mapping types to serve as a trivial wrapper
/// over the Entry interface.
pub trait InsertAndExtend<K, V>: Default {
    /// Creates collection with the given key if necessary
    /// and extends it with the given value.
    fn insert_and_extend(&mut self, key: K, value: V);
}

impl<K, V, E, H> InsertAndExtend<K, V> for HashMap<K, E, H>
where
    K: Eq + Hash,
    E: Default + Extend<V>,
    H: BuildHasher + Default,
{
    #[inline]
    fn insert_and_extend(&mut self, key: K, value: V) {
        self.entry(key).or_default().extend(std::iter::once(value));
    }
}

impl<K, V, E> InsertAndExtend<K, V> for BTreeMap<K, E>
where
    K: Ord,
    E: Default + Extend<V>,
{
    #[inline]
    fn insert_and_extend(&mut self, key: K, value: V) {
        self.entry(key).or_default().extend(std::iter::once(value));
    }
}

/// Implemented by mapping types (`HashMap` and `BTreeMap`)
/// such that they can populated by an iterator.
/// Roughly analogous to the `FromIterator` trait.
pub trait SummarizeFromIterator<V> {
    /// Builds a grouped collection from an iterator of key,value tuples.
    ///
    /// It's recommended to call an iterator's `summarize()` method
    /// rather than call this directly.
    fn summarize_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = V>;
}

impl<K, V, C> SummarizeFromIterator<(K, V)> for C
where
    C: InsertAndIncrement<K, V>,
{
    #[inline]
    fn summarize_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        #[derive(Debug)]
        enum Never {}

        let r: Result<Self, Never> =
            SummarizeFromIterator::summarize_from_iter(iter.into_iter().map(Ok));
        r.unwrap()
    }
}

impl<K, V, C> SummarizeFromIterator<Option<(K, V)>> for Option<C>
where
    C: InsertAndIncrement<K, V>,
{
    #[inline]
    fn summarize_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Option<(K, V)>>,
    {
        let r: Result<C, ()> =
            SummarizeFromIterator::summarize_from_iter(iter.into_iter().map(|o| o.ok_or(())));
        r.ok()
    }
}

impl<K, V, C, E> SummarizeFromIterator<Result<(K, V), E>> for Result<C, E>
where
    C: InsertAndIncrement<K, V>,
{
    fn summarize_from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Result<(K, V), E>>,
    {
        let mut h = C::default();

        for r in iter {
            let (k, v) = r?;
            h.insert_and_increment(k, v);
        }

        Ok(h)
    }
}

/// Extends Iterators with an additional grouping method.
pub trait IntoSummary<V> {
    /// Consumes the iterator and returns a summarized of its contents.
    fn summarize<B: SummarizeFromIterator<V>>(self) -> B;
}

impl<V, I> IntoSummary<V> for I
where
    I: Iterator<Item = V>,
{
    #[inline]
    fn summarize<B: SummarizeFromIterator<V>>(self) -> B {
        B::summarize_from_iter(self)
    }
}

/// A trait for mapping types to serve as a trivial wrapper
/// over the Entry interface
pub trait InsertAndIncrement<K, V>: Default {
    /// Creates collection with the given key if necessary
    /// and increments its total by the given value
    fn insert_and_increment(&mut self, key: K, value: V);
}

impl<K, V, H> InsertAndIncrement<K, V> for HashMap<K, V, H>
where
    K: Eq + Hash,
    V: Default + std::ops::AddAssign,
    H: BuildHasher + Default,
{
    #[inline]
    fn insert_and_increment(&mut self, key: K, value: V) {
        *self.entry(key).or_default() += value;
    }
}

impl<K, V> InsertAndIncrement<K, V> for BTreeMap<K, V>
where
    K: Ord,
    V: Default + std::ops::AddAssign,
{
    #[inline]
    fn insert_and_increment(&mut self, key: K, value: V) {
        *self.entry(key).or_default() += value;
    }
}
