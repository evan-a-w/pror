use crate::bitset::BitSetT;
use std::iter;

/// A storage of fixed‐size blocks of `usize`.
/// The bitset treats each block as `N * usize::BITS` bits.
pub trait BlockStorage<const N: usize>: Sized {
    /// Create a zeroed‐out storage with exactly `blocks` blocks.
    fn with_capacity(blocks: usize) -> Self;
    /// Number of blocks available.
    fn block_count(&self) -> usize;
    /// Shared access to the `i`th `[usize; N]` block.
    fn block(&self, i: usize) -> &[usize; N];
    /// Mutable access to the `i`th `[usize; N]` block.
    fn block_mut(&mut self, i: usize) -> &mut [usize; N];

    fn resize(&mut self, blocks: usize);

    /// Return the index of the first block ≥ `start` with any set bit.
    fn first_set_block_ge(&self, start: usize) -> Option<usize>;
    /// Return the index of the first block containing any set bit.
    /// Default: same as `first_set_block_ge(0)`.
    fn first_set_block(&self) -> Option<usize> {
        self.first_set_block_ge(0)
    }

    /// Return the index of the first block ≥ `start` with any unset bit.
    fn first_unset_block_ge(&self, start: usize) -> Option<usize>;
    /// Return the index of the first block containing any unset bit.
    /// Default: same as `first_unset_block_ge(0)`.
    fn first_unset_block(&self) -> Option<usize> {
        self.first_unset_block_ge(0)
    }
}

/// A resizable bitset atop any `BlockStorage<N>`
#[derive(Clone)]
pub struct BitSet<S, const N: usize>
where
    S: BlockStorage<N> + Clone,
{
    storage: S,
}

/// Generic `BlockStorage` for any container of `[usize; N]` that can be default-constructed,
/// extended, and viewed as a slice of blocks.
impl<S, const N: usize> BlockStorage<N> for S
where
    S: Default + Extend<[usize; N]> + AsRef<[[usize; N]]> + AsMut<[[usize; N]]>,
{
    fn with_capacity(blocks: usize) -> Self {
        let mut s = S::default();
        s.extend(std::iter::repeat([0; N]).take(blocks));
        s
    }

    fn block_count(&self) -> usize {
        self.as_ref().len()
    }

    fn block(&self, i: usize) -> &[usize; N] {
        &self.as_ref()[i]
    }

    fn resize(&mut self, blocks: usize) {
        self.extend(std::iter::repeat([0; N]).take(blocks - self.block_count()));
    }

    fn block_mut(&mut self, i: usize) -> &mut [usize; N] {
        &mut self.as_mut()[i]
    }

    fn first_set_block_ge(&self, start: usize) -> Option<usize> {
        self.as_ref()[start..]
            .iter()
            .position(|blk| blk.iter().any(|&w| w != 0))
            .map(|i| start + i)
    }

    fn first_unset_block_ge(&self, start: usize) -> Option<usize> {
        self.as_ref()[start..]
            .iter()
            .position(|blk| blk.iter().any(|&w| w != usize::MAX))
            .map(|i| start + i)
    }
}

impl<S, const N: usize> BitSet<S, N>
where
    S: BlockStorage<N> + Clone,
{
    /// Bits per block (N words × bits per usize).
    const BITS_PER_BLOCK: usize = N * usize::BITS as usize;

    /// Create a new zeroed bitset with `blocks` blocks.
    pub fn new(blocks: usize) -> Self {
        BitSet {
            storage: S::with_capacity(blocks),
        }
    }

    /// Ensure capacity for at least `bits` bits. Does not shrink.
    pub fn grow(&mut self, bits: usize) {
        let needed_blocks = (bits + Self::BITS_PER_BLOCK - 1) / Self::BITS_PER_BLOCK;
        let current = self.storage.block_count();
        if needed_blocks > current {
            self.storage.resize(needed_blocks);
        }
    }

    /// Total bits currently supported.
    pub fn capacity(&self) -> usize {
        self.storage.block_count() * Self::BITS_PER_BLOCK
    }

    #[inline]
    fn locate(bit: usize) -> (usize, usize, usize) {
        let block_idx = bit / Self::BITS_PER_BLOCK;
        let bit_in_block = bit % Self::BITS_PER_BLOCK;
        let word_idx = bit_in_block / usize::BITS as usize;
        let offset = bit_in_block % usize::BITS as usize;
        (block_idx, word_idx, offset)
    }

    /// Set a bit to 1, growing if needed.
    pub fn set(&mut self, bit: usize) {
        self.grow(bit + 1);
        let (b, w, o) = Self::locate(bit);
        self.storage.block_mut(b)[w] |= 1 << o;
    }

    /// Clear a bit to 0 (no grow).
    pub fn clear(&mut self, bit: usize) {
        if bit >= self.capacity() {
            return;
        }
        let (b, w, o) = Self::locate(bit);
        self.storage.block_mut(b)[w] &= !(1 << o);
    }

    pub fn clear_all(&mut self) {
        for b in 0..self.storage.block_count() {
            let blk = self.storage.block_mut(b);
            for w in blk.iter_mut() {
                *w = 0;
            }
        }
    }

    /// Test if a bit is set (no grow).
    pub fn contains(&self, bit: usize) -> bool {
        if bit >= self.capacity() {
            return false;
        }
        let (b, w, o) = Self::locate(bit);
        (self.storage.block(b)[w] >> o) & 1 != 0
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
        let (start_b, start_w, offset) = Self::locate(bit);
        if start_b >= self.storage.block_count() {
            return None;
        }
        let blk = self.storage.block(start_b);
        let mask = blk[start_w] & (!0usize << offset);
        if mask != 0 {
            return Some(
                start_b * Self::BITS_PER_BLOCK
                    + start_w * usize::BITS as usize
                    + mask.trailing_zeros() as usize,
            );
        }
        for wi in start_w + 1..N {
            let w = blk[wi];
            if w != 0 {
                return Some(
                    start_b * Self::BITS_PER_BLOCK
                        + wi * usize::BITS as usize
                        + w.trailing_zeros() as usize,
                );
            }
        }
        let b2 = self.storage.first_set_block_ge(start_b + 1)?;
        let blk2 = self.storage.block(b2);
        for (wi, &w) in blk2.iter().enumerate() {
            if w != 0 {
                return Some(
                    b2 * Self::BITS_PER_BLOCK
                        + wi * usize::BITS as usize
                        + w.trailing_zeros() as usize,
                );
            }
        }
        None
    }

    /// Find first unset ≥ `bit`.
    pub fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        let (start_b, start_w, offset) = Self::locate(bit);
        if start_b >= self.storage.block_count() {
            return None;
        }
        let blk = self.storage.block(start_b);
        let inv = !blk[start_w] & (!0usize << offset);
        if inv != 0 {
            return Some(
                start_b * Self::BITS_PER_BLOCK
                    + start_w * usize::BITS as usize
                    + inv.trailing_zeros() as usize,
            );
        }
        for wi in start_w + 1..N {
            let w = blk[wi];
            if w != usize::MAX {
                return Some(
                    start_b * Self::BITS_PER_BLOCK
                        + wi * usize::BITS as usize
                        + (!w).trailing_zeros() as usize,
                );
            }
        }
        let b2 = self.storage.first_unset_block_ge(start_b + 1)?;
        let blk2 = self.storage.block(b2);
        for (wi, &w) in blk2.iter().enumerate() {
            if w != usize::MAX {
                return Some(
                    b2 * Self::BITS_PER_BLOCK
                        + wi * usize::BITS as usize
                        + (!w).trailing_zeros() as usize,
                );
            }
        }
        None
    }

    /// Union: grows to other.capacity(), then `self |= other`.
    pub fn union_with(&mut self, other: &Self) {
        self.grow(other.capacity());
        for b in 0..self.storage.block_count().min(other.storage.block_count()) {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a |= bb;
            }
        }
    }

    /// Intersection: no grow.
    pub fn intersect_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count().min(other.storage.block_count()) {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a &= bb;
            }
        }
    }

    pub fn intersect(&mut self, aset: &Self, bset: &Self) {
        let cap = aset.capacity().max(bset.capacity());
        if self.capacity() > cap {
            for i in (cap / Self::BITS_PER_BLOCK)..(self.capacity() / Self::BITS_PER_BLOCK) {
                self.storage.block_mut(i).fill(0);
            }
        } else {
            self.grow(aset.capacity().max(bset.capacity()));
        }
        for bl in 0..aset.storage.block_count().min(bset.storage.block_count()) {
            let me = self.storage.block_mut(bl);
            let a = aset.storage.block(bl);
            let b = bset.storage.block(bl);
            for ((m, &bb), &aa) in me.iter_mut().zip(a.iter()).zip(b.iter()) {
                *m = bb & aa;
            }
        }
    }

    /// Difference: no grow.
    pub fn difference_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count().min(other.storage.block_count()) {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a &= !bb;
            }
        }
    }
    pub fn set_between(&mut self, start: usize, end: usize) {
        if start >= end {
            return;
        }
        self.grow(end);
        let (start_b, start_w, start_o) = Self::locate(start);
        let (end_b, end_w, end_o) = Self::locate(end - 1);
        if start_b == end_b {
            let blk = self.storage.block_mut(start_b);
            let left = !0usize << start_o;
            let right = if end_o + 1 == usize::BITS as usize {
                !0usize
            } else {
                (1usize << (end_o + 1)) - 1
            };
            blk[start_w] |= left & right;
        } else {
            let blk = self.storage.block_mut(start_b);
            blk[start_w] |= !0usize << start_o;
            for wi in (start_w + 1)..N {
                blk[wi] = !0usize;
            }
            for b in (start_b + 1)..end_b {
                let blk = self.storage.block_mut(b);
                for wi in 0..N {
                    blk[wi] = !0usize;
                }
            }
            let blk = self.storage.block_mut(end_b);
            for wi in 0..end_w {
                blk[wi] = !0usize;
            }
            let mask = if end_o + 1 == usize::BITS as usize {
                !0usize
            } else {
                (1usize << (end_o + 1)) - 1
            };
            blk[end_w] |= mask;
        }
    }
    pub fn count(&self) -> usize {
        let mut acc = 0;
        for b in 0..self.storage.block_count() {
            for &w in self.storage.block(b).iter() {
                acc += w.count_ones() as usize;
            }
        }
        acc
    }

    pub fn nth(&self, n: usize) -> Option<usize> {
        let mut count = 0;
        let bits_per_word = usize::BITS as usize;
        for b in 0..self.storage.block_count() {
            let blk = self.storage.block(b);
            for wi in 0..N {
                let w = blk[wi];
                let pop = w.count_ones() as usize;
                if count + pop <= n {
                    count += pop;
                    continue;
                }
                let mut mask = w;
                let mut rem = n - count;
                while mask != 0 {
                    let tz = mask.trailing_zeros() as usize;
                    if rem == 0 {
                        return Some(b * Self::BITS_PER_BLOCK + wi * bits_per_word + tz);
                    }
                    rem -= 1;
                    mask &= !(1 << tz);
                }
            }
        }
        None
    }
}

impl<S, const N: usize> BitSetT for BitSet<S, N>
where
    S: BlockStorage<N> + Extend<[usize; N]> + Clone,
{
    fn grow(&mut self, bits: usize) {
        self.grow(bits);
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
    fn clear_all(&mut self) {
        self.clear_all();
    }
    fn set(&mut self, bit: usize) {
        self.set(bit);
    }

    fn nth(&self, n: usize) -> Option<usize> {
        self.nth(n)
    }

    fn count(&self) -> usize {
        self.count()
    }

    fn set_between(&mut self, a: usize, b: usize) {
        self.set_between(a, b);
    }
    fn clear(&mut self, bit: usize) {
        self.clear(bit);
    }
    fn contains(&self, bit: usize) -> bool {
        self.contains(bit)
    }
    fn first_set(&self) -> Option<usize> {
        self.first_set()
    }
    fn first_unset(&self) -> Option<usize> {
        self.first_unset()
    }
    fn first_set_ge(&self, bit: usize) -> Option<usize> {
        self.first_set_ge(bit)
    }
    fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        self.first_unset_ge(bit)
    }
    fn union_with(&mut self, other: &Self) {
        self.union_with(other);
    }
    fn intersect_with(&mut self, other: &Self) {
        self.intersect_with(other);
    }

    fn intersect(&mut self, a: &Self, b: &Self) {
        self.intersect(a, b);
    }

    fn difference_with(&mut self, other: &Self) {
        self.difference_with(other);
    }

    fn create() -> Self {
        BitSet::<S, N>::new(0)
    }
}
