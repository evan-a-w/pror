use crate::bitset::BitSetT;
use std::iter;

/// Compact bitset backed by a flat vector of machine words.
#[derive(Clone, Default)]
pub struct BitSet {
    words: Vec<usize>,
}

impl BitSet {
    /// Bits per machine word.
    const BITS_PER_WORD: usize = usize::BITS as usize;

    /// Create a bitset with `words` zeroed words of capacity.
    pub fn new(words: usize) -> Self {
        Self {
            words: vec![0; words],
        }
    }

    /// Ensure capacity for at least `bits` bits. Does not shrink.
    pub fn grow(&mut self, bits: usize) {
        let needed_words = (bits + Self::BITS_PER_WORD - 1) / Self::BITS_PER_WORD;
        if needed_words > self.words.len() {
            self.words.resize(needed_words, 0);
        }
    }

    /// Total bits currently supported.
    pub fn capacity(&self) -> usize {
        self.words.len() * Self::BITS_PER_WORD
    }

    #[inline]
    fn locate(bit: usize) -> (usize, usize) {
        let w = bit / Self::BITS_PER_WORD;
        let o = bit % Self::BITS_PER_WORD;
        (w, o)
    }

    /// Set a bit to 1, growing if needed.
    pub fn set(&mut self, bit: usize) {
        self.grow(bit + 1);
        let (w, o) = Self::locate(bit);
        self.words[w] |= 1usize << o;
    }

    /// Clear a bit to 0 (no grow).
    pub fn clear(&mut self, bit: usize) {
        if bit >= self.capacity() {
            return;
        }
        let (w, o) = Self::locate(bit);
        self.words[w] &= !(1usize << o);
    }

    /// Clear all bits to zero.
    pub fn clear_all(&mut self) {
        for w in &mut self.words {
            *w = 0;
        }
    }

    /// Test if a bit is set (no grow).
    pub fn contains(&self, bit: usize) -> bool {
        if bit >= self.capacity() {
            return false;
        }
        let (w, o) = Self::locate(bit);
        (self.words[w] >> o) & 1 != 0
    }

    /// Find the first set bit, or `None`.
    pub fn first_set(&self) -> Option<usize> {
        self.first_set_ge(0)
    }

    /// Find the first unset bit, or `None`.
    pub fn first_unset(&self) -> Option<usize> {
        self.first_unset_ge(0)
    }

    /// Find first set ≥ `bit`.
    pub fn first_set_ge(&self, bit: usize) -> Option<usize> {
        if bit >= self.capacity() {
            return None;
        }
        let (start_w, offset) = Self::locate(bit);

        // Check within the starting word (mask out lower bits).
        let mut w = self.words[start_w] & (!0usize << offset);
        if w != 0 {
            return Some(start_w * Self::BITS_PER_WORD + w.trailing_zeros() as usize);
        }

        // Scan following words.
        for (i, &word) in self.words.iter().enumerate().skip(start_w + 1) {
            if word != 0 {
                return Some(i * Self::BITS_PER_WORD + word.trailing_zeros() as usize);
            }
        }
        None
    }

    /// Find first unset ≥ `bit`.
    pub fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        if bit >= self.capacity() {
            return None;
        }
        let (start_w, offset) = Self::locate(bit);

        // Check within starting word (invert & mask).
        let mut inv = (!self.words[start_w]) & (!0usize << offset);
        if inv != 0 {
            return Some(start_w * Self::BITS_PER_WORD + inv.trailing_zeros() as usize);
        }

        // Scan following words.
        for (i, &word) in self.words.iter().enumerate().skip(start_w + 1) {
            if word != usize::MAX {
                let inv = !word;
                return Some(i * Self::BITS_PER_WORD + inv.trailing_zeros() as usize);
            }
        }
        None
    }

    /// In-place: `self |= other` (grows self if needed).
    pub fn union_with(&mut self, other: &Self) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for i in 0..other.words.len() {
            self.words[i] |= other.words[i];
        }
    }

    /// In-place: `self &= other` (no grow; clears extra words).
    pub fn intersect_with(&mut self, other: &Self) {
        let min = self.words.len().min(other.words.len());
        for i in 0..min {
            self.words[i] &= other.words[i];
        }
        for w in &mut self.words[min..] {
            *w = 0;
        }
    }

    /// In-place: `self &= !other` (no grow).
    pub fn difference_with(&mut self, other: &Self) {
        let min = self.words.len().min(other.words.len());
        for i in 0..min {
            self.words[i] &= !other.words[i];
        }
        // words beyond `other` remain as-is
    }

    /// Set all bits in [start, end). Safe for any range; grows as needed.
    pub fn set_between(&mut self, start: usize, end: usize) {
        if start >= end {
            return;
        }
        self.grow(end);

        let (s_w, s_o) = Self::locate(start);
        let (e_w, e_o) = Self::locate(end - 1);

        if s_w == e_w {
            // Single word range.
            let left = !0usize << s_o;
            let right = if e_o + 1 == Self::BITS_PER_WORD {
                !0usize
            } else {
                (1usize << (e_o + 1)) - 1
            };
            self.words[s_w] |= left & right;
            return;
        }

        // Head word.
        self.words[s_w] |= !0usize << s_o;
        for w in &mut self.words[s_w + 1..e_w] {
            *w = !0usize;
        }

        // Tail word.
        let tail_mask = if e_o + 1 == Self::BITS_PER_WORD {
            !0usize
        } else {
            (1usize << (e_o + 1)) - 1
        };
        self.words[e_w] |= tail_mask;
    }

    /// Count number of set bits.
    pub fn count(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Return the index of the n-th set bit (0-based), or `None`.
    pub fn nth(&self, n: usize) -> Option<usize> {
        let mut seen = 0usize;
        for (i, &w) in self.words.iter().enumerate() {
            let pop = w.count_ones() as usize;
            if seen + pop <= n {
                seen += pop;
                continue;
            }
            // The target is in this word.
            let mut mask = w;
            let mut rem = n - seen;
            while mask != 0 {
                let tz = mask.trailing_zeros() as usize;
                if rem == 0 {
                    return Some(i * Self::BITS_PER_WORD + tz);
                }
                rem -= 1;
                mask &= !(1usize << tz);
            }
        }
        None
    }

    #[inline]
    fn usize_iter_ones(mut x: usize) -> impl Iterator<Item = usize> {
        iter::from_fn(move || {
            if x == 0 {
                return None;
            }
            let tz = x.trailing_zeros() as usize;
            x &= x - 1; // clear lowest set bit
            Some(tz)
        })
    }

    #[inline]
    fn iter_word_bits(word: usize, base_bit: usize) -> impl Iterator<Item = usize> {
        Self::usize_iter_ones(word).map(move |off| base_bit + off)
    }

    /// Iterate indices in `self ∪ other`.
    pub fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let min = self.words.len().min(other.words.len());
        let head = (0..min).flat_map(move |i| {
            let w = self.words[i] | other.words[i];
            Self::iter_word_bits(w, i * Self::BITS_PER_WORD)
        });
        let (longer, start) = if self.words.len() > other.words.len() {
            (&self.words, other.words.len())
        } else {
            (&other.words, self.words.len())
        };
        head.chain(
            (start..longer.len())
                .flat_map(move |i| Self::iter_word_bits(longer[i], i * Self::BITS_PER_WORD)),
        )
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
        (0..self.words.len()).flat_map(move |i| {
            let w = self.words[i];
            Self::iter_word_bits(w, i * Self::BITS_PER_WORD)
        })
    }

    /// Iterate indices in `self ∩ other`, starting at `ge`.
    pub fn iter_intersection_ge<'a>(
        &'a self,
        other: &'a Self,
        ge: usize,
    ) -> impl Iterator<Item = usize> + 'a {
        let start_word = ge / Self::BITS_PER_WORD;
        let offset = ge % Self::BITS_PER_WORD;
        let min = self.words.len().min(other.words.len());

        (start_word..min).flat_map(move |i| {
            let mut w = self.words[i] & other.words[i];
            if i == start_word {
                w &= !0usize << offset;
            }
            Self::iter_word_bits(w, i * Self::BITS_PER_WORD)
        })
    }

    /// Iterate indices in `self ∩ other`.
    pub fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let min = self.words.len().min(other.words.len());
        (0..min).flat_map(move |i| {
            let w = self.words[i] & other.words[i];
            Self::iter_word_bits(w, i * Self::BITS_PER_WORD)
        })
    }

    /// Iterate indices in `self \ other`.
    pub fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let min = self.words.len().min(other.words.len());
        let head = (0..min).flat_map(move |i| {
            let w = self.words[i] & !other.words[i];
            Self::iter_word_bits(w, i * Self::BITS_PER_WORD)
        });
        head.chain(
            (min..self.words.len())
                .flat_map(move |i| Self::iter_word_bits(self.words[i], i * Self::BITS_PER_WORD)),
        )
    }

    /// `self = a ∩ b`, resizing `self` to max(a,b) capacity and clearing the rest.
    pub fn intersect(&mut self, a: &Self, b: &Self) {
        let max_words = a.words.len().max(b.words.len());
        if self.words.len() > max_words {
            for w in &mut self.words[max_words..] {
                *w = 0;
            }
        } else if self.words.len() < max_words {
            self.words.resize(max_words, 0);
        }

        let min = a.words.len().min(b.words.len());
        for i in 0..min {
            self.words[i] = a.words[i] & b.words[i];
        }
        for w in &mut self.words[min..] {
            *w = 0;
        }
    }

    /// First bit of `self ∩ other`, or None.
    pub fn intersect_first_set(&self, other: &Self) -> Option<usize> {
        self.iter_intersection(other).next()
    }

    /// First bit of `self ∩ other` with index ≥ `ge`, or None.
    pub fn intersect_first_set_ge(&self, other: &Self, ge: usize) -> Option<usize> {
        self.iter_intersection_ge(other, ge).next()
    }
}

impl BitSetT for BitSet {
    fn create() -> Self {
        BitSet::new(0)
    }

    fn grow(&mut self, bits: usize) {
        BitSet::grow(self, bits)
    }
    fn capacity(&self) -> usize {
        BitSet::capacity(self)
    }
    fn clear_all(&mut self) {
        BitSet::clear_all(self)
    }
    fn set(&mut self, bit: usize) {
        BitSet::set(self, bit)
    }
    fn set_between(&mut self, start: usize, end: usize) {
        BitSet::set_between(self, start, end)
    }
    fn clear(&mut self, bit: usize) {
        BitSet::clear(self, bit)
    }
    fn contains(&self, bit: usize) -> bool {
        BitSet::contains(self, bit)
    }
    fn first_set(&self) -> Option<usize> {
        BitSet::first_set(self)
    }
    fn first_unset(&self) -> Option<usize> {
        BitSet::first_unset(self)
    }
    fn first_set_ge(&self, bit: usize) -> Option<usize> {
        BitSet::first_set_ge(self, bit)
    }
    fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        BitSet::first_unset_ge(self, bit)
    }
    fn union_with(&mut self, other: &Self) {
        BitSet::union_with(self, other)
    }
    fn intersect_with(&mut self, other: &Self) {
        BitSet::intersect_with(self, other)
    }
    fn intersect(&mut self, a: &Self, b: &Self) {
        BitSet::intersect(self, a, b)
    }
    fn difference_with(&mut self, other: &Self) {
        BitSet::difference_with(self, other)
    }
    fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        BitSet::iter_union(self, other)
    }
    fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        BitSet::iter_intersection(self, other)
    }
    fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        BitSet::iter_difference(self, other)
    }
    fn count(&self) -> usize {
        BitSet::count(self)
    }
    fn nth(&self, n: usize) -> Option<usize> {
        BitSet::nth(self, n)
    }
    fn intersect_first_set(&self, other: &Self) -> Option<usize> {
        BitSet::intersect_first_set(self, other)
    }
    fn intersect_first_set_ge(&self, other: &Self, ge: usize) -> Option<usize> {
        BitSet::intersect_first_set_ge(self, other, ge)
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
        self.iter()
    }
}
