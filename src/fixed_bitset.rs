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

impl<const N: usize> BlockStorage<N> for Vec<[usize; N]> {
    fn with_capacity(blocks: usize) -> Self {
        vec![[0; N]; blocks]
    }
    fn block_count(&self) -> usize {
        self.len()
    }
    fn block(&self, i: usize) -> &[usize; N] {
        &self[i]
    }
    fn block_mut(&mut self, i: usize) -> &mut [usize; N] {
        &mut self[i]
    }

    fn first_set_block_ge(&self, start: usize) -> Option<usize> {
        (start..self.len()).find(|&i| self[i].iter().any(|&w| w != 0))
    }

    fn first_unset_block_ge(&self, start: usize) -> Option<usize> {
        (start..self.len()).find(|&i| self[i].iter().any(|&w| w != usize::MAX))
    }
}

/// A fixed‐size bitset atop any `BlockStorage<N>`.
pub struct BitSet<S, const N: usize>
where
    S: BlockStorage<N>,
{
    storage: S,
}

impl<S, const N: usize> BitSet<S, N>
where
    S: BlockStorage<N>,
{
    /// Bits per block (N words × bits per usize).
    const BITS_PER_BLOCK: usize = N * usize::BITS as usize;

    /// Create a new zeroed bitset with `blocks` blocks.
    pub fn new(blocks: usize) -> Self {
        BitSet { storage: S::with_capacity(blocks) }
    }

    /// Total bits = blocks × bits_per_block.
    pub fn capacity(&self) -> usize {
        self.storage.block_count() * Self::BITS_PER_BLOCK
    }

    /// Helper to locate a global bit index:
    /// returns (block_index, word_index, bit_offset).
    #[inline]
    fn locate(bit: usize) -> (usize, usize, usize) {
        let block_idx = bit / Self::BITS_PER_BLOCK;
        let bit_in_block = bit % Self::BITS_PER_BLOCK;
        let word_idx = bit_in_block / usize::BITS as usize;
        let offset = bit_in_block % usize::BITS as usize;
        (block_idx, word_idx, offset)
    }

    /// Clear all bits.
    pub fn clear_all(&mut self) {
        for i in 0..self.storage.block_count() {
            self.storage.block_mut(i).fill(0);
        }
    }

    /// Set a bit to 1.
    pub fn set(&mut self, bit: usize) {
        let (b, w, o) = Self::locate(bit);
        self.storage.block_mut(b)[w] |= 1 << o;
    }

    /// Clear a bit to 0.
    pub fn clear(&mut self, bit: usize) {
        let (b, w, o) = Self::locate(bit);
        self.storage.block_mut(b)[w] &= !(1 << o);
    }

    /// Test if a bit is set.
    pub fn contains(&self, bit: usize) -> bool {
        let (b, w, o) = Self::locate(bit);
        (self.storage.block(b)[w] >> o) & 1 != 0
    }

    /// Find the first set bit in the entire bitset.
    /// Wraps `first_set_ge(0)` to avoid code duplication.
    pub fn first_set(&self) -> Option<usize> {
        self.first_set_ge(0)
    }

    /// Find the first unset bit in the entire bitset.
    /// Wraps `first_unset_ge(0)` to avoid code duplication.
    pub fn first_unset(&self) -> Option<usize> {
        self.first_unset_ge(0)
    }

    /// Find the first set bit ≥ `bit`.
    pub fn first_set_ge(&self, bit: usize) -> Option<usize> {
        let (start_b, start_w, offset) = Self::locate(bit);
        if start_b >= self.storage.block_count() {
            return None;
        }
        let blk = self.storage.block(start_b);
        let mask = blk[start_w] & (!0usize << offset);
        if mask != 0 {
            let tz = mask.trailing_zeros() as usize;
            return Some(start_b * Self::BITS_PER_BLOCK
                        + start_w * usize::BITS as usize
                        + tz);
        }
        for wi in (start_w + 1)..N {
            let w = blk[wi];
            if w != 0 {
                let tz = w.trailing_zeros() as usize;
                return Some(start_b * Self::BITS_PER_BLOCK
                            + wi * usize::BITS as usize
                            + tz);
            }
        }
        let b2 = self.storage.first_set_block_ge(start_b + 1)?;
        let blk2 = self.storage.block(b2);
        for (w_i, &w) in blk2.iter().enumerate() {
            if w != 0 {
                let tz = w.trailing_zeros() as usize;
                return Some(b2 * Self::BITS_PER_BLOCK
                            + w_i * usize::BITS as usize
                            + tz);
            }
        }
        None
    }

    /// Find the first unset bit ≥ `bit`.
    pub fn first_unset_ge(&self, bit: usize) -> Option<usize> {
        let (start_b, start_w, offset) = Self::locate(bit);
        if start_b >= self.storage.block_count() {
            return None;
        }
        let blk = self.storage.block(start_b);
        let inv = !blk[start_w] & (!0usize << offset);
        if inv != 0 {
            let tz = inv.trailing_zeros() as usize;
            return Some(start_b * Self::BITS_PER_BLOCK
                        + start_w * usize::BITS as usize
                        + tz);
        }
        for wi in (start_w + 1)..N {
            let w = blk[wi];
            if w != usize::MAX {
                let tz = (!w).trailing_zeros() as usize;
                return Some(start_b * Self::BITS_PER_BLOCK
                            + wi * usize::BITS as usize
                            + tz);
            }
        }
        let b2 = self.storage.first_unset_block_ge(start_b + 1)?;
        let blk2 = self.storage.block(b2);
        for (w_i, &w) in blk2.iter().enumerate() {
            if w != usize::MAX {
                let tz = (!w).trailing_zeros() as usize;
                return Some(b2 * Self::BITS_PER_BLOCK
                            + w_i * usize::BITS as usize
                            + tz);
            }
        }
        None
    }

    /// In‐place union: `self |= other`.
    pub fn union_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count() {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a |= bb;
            }
        }
    }

    /// In‐place intersection: `self &= other`.
    pub fn intersect_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count() {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a &= bb;
            }
        }
    }

    /// In‐place difference: `self &= !other`.
    pub fn difference_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count() {
            let me = self.storage.block_mut(b);
            let them = other.storage.block(b);
            for (a, &bb) in me.iter_mut().zip(them.iter()) {
                *a &= !bb;
            }
        }
    }
}

