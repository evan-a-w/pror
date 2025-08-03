use std::iter;
use std::ops::Bound;

/// A generic BitSet interface capturing common bitset operations.
pub trait BitSetT {
    fn create() -> Self;
    /// Ensure capacity for at least `bits` bits. Does not shrink.
    fn grow(&mut self, bits: usize);
    /// Total number of bits currently supported.
    fn capacity(&self) -> usize;
    /// Clear all bits to zero.
    fn clear_all(&mut self);
    /// Set a bit to 1, resizing if necessary.
    fn set(&mut self, bit: usize);

    fn set_between(&mut self, start_bit_incl: usize, end_bit_excl: usize);

    /// Clear a bit to 0.
    fn clear(&mut self, bit: usize);
    /// Test if a bit is set.
    fn contains(&self, bit: usize) -> bool;

    /// Find the first set bit, or `None`.
    fn first_set(&self) -> Option<usize>;
    /// Find the first unset bit, or `None`.
    fn first_unset(&self) -> Option<usize>;
    /// Find the first set bit ≥ `bit`.
    fn first_set_ge(&self, bit: usize) -> Option<usize>;
    /// Find the first unset bit ≥ `bit`.
    fn first_unset_ge(&self, bit: usize) -> Option<usize>;

    /// In-place union: `self |= other`.
    fn union_with(&mut self, other: &Self);

    /// In-place intersection: `self &= other`.
    fn intersect_with(&mut self, other: &Self);
    /// In-place difference: `self &= !other`.
    fn difference_with(&mut self, other: &Self);

    fn intersect(&mut self, a: &Self, b: &Self);

    fn nth(&self, n: usize) -> Option<usize>;

    fn count(&self) -> usize;

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let mut after = 0;
        iter::from_fn(move || {
            let res = self.first_set_ge(after);
            if let Some(res) = res {
                after = res + 1;
                Some(res)
            } else {
                None
            }
        })
    }

    // TODO: try specialize and make faster
    fn intersect_first_set_ge(&self, other: &impl BitSetT, ge: usize) -> Option<usize> {
        match (self.first_set_ge(ge), other.first_set_ge(ge)) {
            (Some(a), Some(b)) if a == b => Some(a),
            (Some(a), Some(b)) if a < b => self.intersect_first_set_ge(other, b),
            (Some(a), Some(_)) => self.intersect_first_set_ge(other, a),
            (Some(_), None) | (None, Some(_)) | (None, None) => None,
        }
    }

    fn intersect_first_set(&self, other: &impl BitSetT) -> Option<usize> {
        self.intersect_first_set_ge(other, 0)
    }

    fn is_empty(&self) -> bool {
        self.first_set().is_none()
    }

    fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let mut next_idx = 0;
        iter::from_fn(move || {
            loop {
                // find next candidate in either set
                let a = self.first_set_ge(next_idx);
                let b = other.first_set_ge(next_idx);
                let bit = match (a, b) {
                    (Some(x), Some(y)) => Some(x.min(y)),
                    (Some(x), None) => Some(x),
                    (None, Some(y)) => Some(y),
                    (None, None) => None,
                };
                match bit {
                    Some(i) => {
                        next_idx = i + 1;
                        return Some(i);
                    }
                    None => return None,
                }
            }
        })
    }

    fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let mut next_idx = 0;
        iter::from_fn(move || {
            loop {
                // scan self for next set bit...
                if let Some(i) = self.first_set_ge(next_idx) {
                    next_idx = i + 1;
                    if other.contains(i) {
                        return Some(i);
                    } else {
                        continue;
                    }
                }
                return None;
            }
        })
    }

    fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let mut next_idx = 0;
        iter::from_fn(move || {
            loop {
                // scan self for next set bit not in other...
                if let Some(i) = self.first_set_ge(next_idx) {
                    next_idx = i + 1;
                    if !other.contains(i) {
                        return Some(i);
                    } else {
                        continue;
                    }
                }
                return None;
            }
        })
    }
}

#[derive(Clone, Debug)]
pub struct BTreeBitSet {
    set: std::collections::BTreeSet<usize>,
}

impl BTreeBitSet {
    fn max_elem_plus_one(&self) -> usize {
        self.set.iter().rev().next().map(|x| x + 1).unwrap_or(0)
    }
}

impl BitSetT for BTreeBitSet {
    fn create() -> Self {
        Self {
            set: std::collections::BTreeSet::new(),
        }
    }

    /// No-op: BTreeSet grows dynamically. We maintain capacity as max element + 1.
    fn grow(&mut self, _bits: usize) {}

    fn capacity(&self) -> usize {
        // capacity is the minimum number of bits needed to represent current content
        self.max_elem_plus_one()
    }

    fn clear_all(&mut self) {
        self.set.clear();
    }

    fn set(&mut self, bit: usize) {
        self.set.insert(bit);
    }

    fn set_between(&mut self, start_bit_incl: usize, end_bit_excl: usize) {
        if start_bit_incl >= end_bit_excl {
            return;
        }
        for i in start_bit_incl..end_bit_excl {
            self.set.insert(i);
        }
    }

    fn clear(&mut self, bit: usize) {
        self.set.remove(&bit);
    }

    fn contains(&self, bit: usize) -> bool {
        self.set.contains(&bit)
    }

    fn first_set(&self) -> Option<usize> {
        self.set.iter().next().copied()
    }

    fn first_unset(&self) -> Option<usize> {
        self.first_unset_ge(0)
    }

    fn first_set_ge(&self, bit: usize) -> Option<usize> {
        self.set
            .range((Bound::Included(bit), Bound::Unbounded))
            .next()
            .copied()
    }

    fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        // Walk through set starting from bit, looking for gaps.
        let mut expected = bit;
        for &s in self.set.range((Bound::Included(bit), Bound::Unbounded)) {
            if s > expected {
                return Some(expected);
            } else if s == expected {
                expected += 1;
            } else {
                // s < expected (shouldn't happen because range is >= bit), skip
            }
        }
        Some(expected)
    }

    fn union_with(&mut self, other: &Self) {
        for &x in &other.set {
            self.set.insert(x);
        }
    }

    fn intersect_with(&mut self, other: &Self) {
        self.set = self
            .set
            .intersection(&other.set)
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
    }

    fn difference_with(&mut self, other: &Self) {
        self.set = self
            .set
            .difference(&other.set)
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
    }

    fn intersect(&mut self, a: &Self, b: &Self) {
        self.set = a
            .set
            .intersection(&b.set)
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
    }

    fn nth(&self, n: usize) -> Option<usize> {
        self.set.iter().nth(n).copied()
    }

    fn count(&self) -> usize {
        self.set.len()
    }
}

// Optional: expose iterator helpers similar to trait defaults
impl BTreeBitSet {
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.set.iter().copied()
    }

    pub fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let mut a_iter = self.set.iter().peekable();
        let mut b_iter = other.set.iter().peekable();
        iter::from_fn(move || loop {
            match (a_iter.peek(), b_iter.peek()) {
                (Some(&&a), Some(&&b)) => {
                    if a < b {
                        a_iter.next();
                        return Some(a);
                    } else if b < a {
                        b_iter.next();
                        return Some(b);
                    } else {
                        a_iter.next();
                        b_iter.next();
                        return Some(a);
                    }
                }
                (Some(&&a), None) => {
                    a_iter.next();
                    return Some(a);
                }
                (None, Some(&&b)) => {
                    b_iter.next();
                    return Some(b);
                }
                (None, None) => return None,
            }
        })
    }

    pub fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        self.set
            .intersection(&other.set)
            .copied()
            .collect::<Vec<_>>()
            .into_iter()
    }

    pub fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        self.set
            .difference(&other.set)
            .copied()
            .collect::<Vec<_>>()
            .into_iter()
    }
}
