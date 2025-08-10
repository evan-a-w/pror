use crate::bitset::BitSetT;
use crate::pool::*;
use std::collections::BTreeMap;
use std::iter;
use std::mem::MaybeUninit;

/// A storage of fixed‐size blocks of `usize`.
/// The bitset treats each block as `N * usize::BITS` bits.
pub trait BlockStorage<const N: usize>: Sized {
    /// Create a zeroed‐out storage with exactly `blocks` blocks.
    fn with_capacity(blocks: usize) -> Self;
    /// Number of blocks available.
    fn block_count(&self) -> usize;
    /// Shared access to the `i`th `[usize; N]` block.
    fn block(&self, i: usize) -> &[usize; N];

    fn get_idx(&self, b: usize, i: usize) -> usize {
        self.block(b)[i]
    }
    fn set_idx(&mut self, b: usize, i: usize, with: usize);

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

    fn set_idx(&mut self, b: usize, i: usize, with: usize) {
        self.as_mut()[b][i] = with;
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
        self.storage
            .set_idx(b, w, self.storage.get_idx(b, w) | (1 << o));
    }

    /// Clear a bit to 0 (no grow).
    pub fn clear(&mut self, bit: usize) {
        if bit >= self.capacity() {
            return;
        }
        let (b, w, o) = Self::locate(bit);
        self.storage
            .set_idx(b, w, self.storage.get_idx(b, w) & !(1 << o));
    }

    pub fn clear_all(&mut self) {
        for b in 0..self.storage.block_count() {
            for i in 0..N {
                self.storage.set_idx(b, i, 0);
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
            let them = other.storage.block(b);
            for (i, &bb) in (0..N).zip(them.iter()) {
                self.storage.set_idx(b, i, self.storage.get_idx(b, i) | bb);
            }
        }
    }

    /// Intersection: no grow.
    pub fn intersect_with(&mut self, other: &Self) {
        let min = self.storage.block_count().min(other.storage.block_count());
        for b in 0..min {
            let them = other.storage.block(b);
            for (i, &bb) in (0..N).zip(them.iter()) {
                self.storage.set_idx(b, i, self.storage.get_idx(b, i) & bb);
            }
        }
        for b in min..(self.storage.block_count()) {
            for i in 0..N {
                self.storage.set_idx(b, i, 0);
            }
        }
    }

    /// Difference: no grow.
    pub fn difference_with(&mut self, other: &Self) {
        for b in 0..self.storage.block_count().min(other.storage.block_count()) {
            let them = other.storage.block(b);
            for (i, &bb) in (0..N).zip(them.iter()) {
                self.storage.set_idx(b, i, self.storage.get_idx(b, i) & !bb);
            }
        }
    }

    fn usize_iter_ones(x: usize) -> impl Iterator<Item = usize> {
        let mut mask = x;
        iter::from_fn(move || {
            if mask == 0 {
                return None;
            }
            let tz = mask.trailing_zeros() as usize;
            let idx = tz + 1;
            mask &= !(1 << tz);
            Some(idx - 1)
        })
    }

    fn iter_bit_indices<'a, I: Iterator<Item = usize> + 'a>(
        words: I,
        block_index: usize,
    ) -> impl Iterator<Item = usize> + 'a
    where
        S: 'a,
    {
        words.enumerate().flat_map(move |(wi, w)| {
            Self::usize_iter_ones(w)
                .map(move |x| block_index * Self::BITS_PER_BLOCK + wi * usize::BITS as usize + x)
        })
    }

    pub fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let for_extra = if self.storage.block_count() > other.storage.block_count() {
            self
        } else {
            other
        };
        let min = self.storage.block_count().min(other.storage.block_count());
        let extra = (min..for_extra.storage.block_count()).flat_map(move |b| {
            Self::iter_bit_indices(for_extra.storage.block(b).iter().copied(), b)
        });
        (0..min)
            .flat_map(move |b| {
                Self::iter_bit_indices(
                    self.storage
                        .block(b)
                        .iter()
                        .zip(other.storage.block(b).iter())
                        .map(move |(&a, &b)| a | b),
                    b,
                )
            })
            .chain(extra)
    }

    pub fn iter_intersection_ge<'a>(
        &'a self,
        other: &'a Self,
        ge: usize,
    ) -> impl Iterator<Item = usize> + 'a {
        let min = self.storage.block_count().min(other.storage.block_count());
        let first_block = ge / Self::BITS_PER_BLOCK;
        let first_block_iter = (first_block..min.min(first_block + 1)).flat_map(move |b| {
            Self::iter_bit_indices(
                self.storage
                    .block(b)
                    .iter()
                    .enumerate()
                    .zip(other.storage.block(b).iter())
                    .map(move |((i, &a), &b)| {
                        if i == 0 {
                            let num_to_zero = ge % Self::BITS_PER_BLOCK;
                            if num_to_zero == usize::BITS as usize {
                                println!("max {num_to_zero}");
                                0
                            } else if num_to_zero == (usize::BITS - 1) as usize {
                                println!("less max {num_to_zero}");
                                a & b & (1 << num_to_zero)
                            } else {
                                println!("less less max {num_to_zero}");
                                a & b & !((1 << num_to_zero) - 1)
                            }
                        } else {
                            a & b
                        }
                    }),
                b,
            )
        });
        let non_cut_off = ((first_block + 1)..min).flat_map(move |b| {
            Self::iter_bit_indices(
                self.storage
                    .block(b)
                    .iter()
                    .zip(other.storage.block(b).iter())
                    .map(move |(&a, &b)| a & b),
                b,
            )
        });
        first_block_iter.chain(non_cut_off)
    }

    pub fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let min = self.storage.block_count().min(other.storage.block_count());
        (0..min).flat_map(move |b| {
            Self::iter_bit_indices(
                self.storage
                    .block(b)
                    .iter()
                    .zip(other.storage.block(b).iter())
                    .map(move |(&a, &b)| a & b),
                b,
            )
        })
    }

    pub fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        let min = self.storage.block_count().min(other.storage.block_count());
        let extra = (min..self.storage.block_count())
            .flat_map(move |b| Self::iter_bit_indices(self.storage.block(b).iter().copied(), b));
        (0..min)
            .flat_map(move |b| {
                Self::iter_bit_indices(
                    self.storage
                        .block(b)
                        .iter()
                        .zip(other.storage.block(b).iter())
                        .map(move |(&a, &b)| a & !b),
                    b,
                )
            })
            .chain(extra)
    }

    pub fn intersect(&mut self, aset: &Self, bset: &Self) {
        let cap = aset.capacity().max(bset.capacity());
        if self.capacity() > cap {
            // clear extra blocks beyond cap
            let start_blk = cap / Self::BITS_PER_BLOCK;
            let end_blk = self.storage.block_count();
            for b in start_blk..end_blk {
                for wi in 0..N {
                    self.storage.set_idx(b, wi, 0);
                }
            }
        } else {
            self.grow(cap);
        }

        let min_blocks = aset.storage.block_count().min(bset.storage.block_count());
        for bl in 0..min_blocks {
            for wi in 0..N {
                let a_word = aset.storage.get_idx(bl, wi);
                let b_word = bset.storage.get_idx(bl, wi);
                self.storage.set_idx(bl, wi, a_word & b_word);
            }
        }

        // clear any remaining blocks (if any) between min_blocks and current capacity
        for b in (min_blocks)..self.storage.block_count() {
            for wi in 0..N {
                self.storage.set_idx(b, wi, 0);
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
            let left = !0usize << start_o;
            let right = if end_o + 1 == usize::BITS as usize {
                !0usize
            } else {
                (1usize << (end_o + 1)) - 1
            };
            let prev = self.storage.get_idx(start_b, start_w);
            self.storage
                .set_idx(start_b, start_w, prev | (left & right));
        } else {
            // start block: from start_o to end of word
            let prev_start = self.storage.get_idx(start_b, start_w);
            self.storage
                .set_idx(start_b, start_w, prev_start | (!0usize << start_o));
            for wi in (start_w + 1)..N {
                self.storage.set_idx(start_b, wi, !0usize);
            }

            // full blocks between
            for b in (start_b + 1)..end_b {
                for wi in 0..N {
                    self.storage.set_idx(b, wi, !0usize);
                }
            }

            // end block: from 0 to end_o
            for wi in 0..end_w {
                self.storage.set_idx(end_b, wi, !0usize);
            }
            let mask = if end_o + 1 == usize::BITS as usize {
                !0usize
            } else {
                (1usize << (end_o + 1)) - 1
            };
            let prev_end = self.storage.get_idx(end_b, end_w);
            self.storage.set_idx(end_b, end_w, prev_end | mask);
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
    S: BlockStorage<N> + Clone,
{
    fn intersect_first_set_ge(&self, other: &Self, ge: usize) -> Option<usize> {
        self.iter_intersection_ge(other, ge).next()
    }
    fn intersect_first_set(&self, other: &Self) -> Option<usize> {
        self.iter_intersection(other).next()
    }

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

    fn iter_union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        self.iter_union(other)
    }

    fn iter_intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        self.iter_intersection(other)
    }

    fn iter_difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = usize> + 'a {
        self.iter_difference(other)
    }

    fn create() -> Self {
        BitSet::<S, N>::new(0)
    }
}

pub type DefaultBitSet = BitSet<Vec<[usize; 1]>, 1>;
pub type DefaultMapBitSet = BitSet<BTreeMapStorage<32>, 32>;

/// Storage where blocks are kept sparsely, but capacity is explicit.
/// Blocks that are all-zero are not stored; when a stored block becomes all-zero it's evicted.
pub struct BTreeMapStorage<const N: usize> {
    map: BTreeMap<usize, Box<[usize; N]>>,
    pool: Pool<Box<[usize; N]>>,
    capacity: usize,             // number of blocks of addressable space
    zero_block: Box<[usize; N]>, // shared all-zero block for reads
}

impl<const N: usize> Clone for BTreeMapStorage<N> {
    fn clone(&self) -> Self {
        BTreeMapStorage {
            map: self.map.clone(),
            pool: Pool::new(), // Pool is not cloned; it will be empty in the clone.
            capacity: self.capacity,
            zero_block: self.zero_block.clone(),
        }
    }
}

impl<const N: usize> BTreeMapStorage<N> {
    fn make_zeroed_block() -> Box<[usize; N]> {
        Box::new([0; N])
    }

    /// Helper to test if a block is all ones.
    fn is_full_block(block: &[usize; N]) -> bool {
        block.iter().all(|&w| w == usize::MAX)
    }

    /// Helper to test if a block is all zero.
    fn is_zero_block(block: &[usize; N]) -> bool {
        block.iter().all(|&w| w == 0)
    }

    /// Get mutable block, creating if missing (with zero contents).
    fn get_or_create_block(&mut self, index: usize) -> &mut [usize; N] {
        if index >= self.capacity {
            panic!(
                "Index {} out of capacity {}: must resize before accessing beyond capacity",
                index, self.capacity
            );
        }
        if !self.map.contains_key(&index) {
            let mut block = self.pool.acquire(|| Self::make_zeroed_block());
            self.map.insert(index, block);
        }
        self.map.get_mut(&index).map(|b| &mut **b).unwrap()
    }

    /// Possibly remove block if it became all zero, returning it to pool.
    fn drop_if_zero(&mut self, index: usize) {
        if let Some(block) = self.map.get(&index) {
            if Self::is_zero_block(block) {
                let block = self.map.remove(&index).unwrap();
                self.pool.release(block);
            }
        }
    }
}

impl<const N: usize> Default for BTreeMapStorage<N> {
    fn default() -> Self {
        BTreeMapStorage {
            map: BTreeMap::new(),
            pool: Pool::new(),
            capacity: 0,
            zero_block: Self::make_zeroed_block(),
        }
    }
}

impl<const N: usize> BlockStorage<N> for BTreeMapStorage<N> {
    fn with_capacity(blocks: usize) -> Self {
        BTreeMapStorage {
            map: BTreeMap::new(),
            pool: Pool::new(),
            capacity: blocks,
            zero_block: Self::make_zeroed_block(),
        }
    }

    fn block_count(&self) -> usize {
        self.capacity
    }

    fn block(&self, i: usize) -> &[usize; N] {
        if i >= self.capacity {
            panic!("Accessing block {} beyond capacity {}", i, self.capacity);
        }
        self.map
            .get(&i)
            .map(|b| &**b)
            .unwrap_or_else(|| &*self.zero_block)
    }

    fn set_idx(&mut self, b: usize, i: usize, with: usize) {
        if b >= self.capacity {
            panic!(
                "Setting index in block {} beyond capacity {}: call resize first",
                b, self.capacity
            );
        }
        let block = self.get_or_create_block(b);
        block[i] = with;
        if Self::is_zero_block(block) {
            self.drop_if_zero(b);
        }
    }

    fn resize(&mut self, blocks: usize) {
        if blocks > self.capacity {
            self.capacity = blocks;
        }
        // shrinking is a no-op; capacity only increases. Stored blocks beyond new capacity
        // are not removed to avoid unexpected data loss.
    }

    fn first_set_block_ge(&self, start: usize) -> Option<usize> {
        if start >= self.capacity {
            return None;
        }
        // find first stored block >= start that has any nonzero word
        self.map
            .range(start..self.capacity)
            .find_map(|(&idx, block)| {
                if !Self::is_zero_block(block) {
                    Some(idx)
                } else {
                    None
                }
            })
    }

    fn first_unset_block_ge(&self, start: usize) -> Option<usize> {
        if start >= self.capacity {
            return None;
        }

        // If a block is missing, it's all zero => has unset bits.
        if !self.map.contains_key(&start) {
            return Some(start);
        }

        // If present and not full, it has unset bits.
        if let Some(block) = self.map.get(&start) {
            if !Self::is_full_block(block) {
                return Some(start);
            }
        }

        // Scan forward within capacity.
        let mut prev = start;
        // iterate over stored blocks >= start+1
        for (&idx, block) in self.map.range((start + 1)..self.capacity) {
            if idx > prev + 1 {
                // gap: implicit zero block
                return Some(prev + 1);
            }
            if !Self::is_full_block(block) {
                return Some(idx);
            }
            prev = idx;
        }

        // If we haven't exhausted capacity, the next after last considered (if < capacity) is a zero gap.
        if prev + 1 < self.capacity {
            return Some(prev + 1);
        }

        // No unset block found.
        None
    }
}
