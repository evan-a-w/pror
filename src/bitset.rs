use std::iter;

/// A generic BitSet interface capturing common bitset operations.
pub trait BitSetT {
    /// Ensure capacity for at least `bits` bits. Does not shrink.
    fn grow(&mut self, bits: usize);
    /// Total number of bits currently supported.
    fn capacity(&self) -> usize;
    /// Clear all bits to zero.
    fn clear_all(&mut self);
    /// Set a bit to 1, resizing if necessary.
    fn set(&mut self, bit: usize);
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
