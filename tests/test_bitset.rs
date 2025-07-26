#[cfg(test)]
mod tests {
    use pror::fixed_bitset::*;

    // Use 1 word per block (64 bits per block)
    type BS1 = BitSet<Vec<[usize; 1]>, 1>;

    #[test]
    fn test_capacity_and_clear() {
        let mut bs = BS1::new(2);
        assert_eq!(bs.capacity(), 2 * usize::BITS as usize);
        // all bits unset
        assert_eq!(bs.first_set(), None);
        assert_eq!(bs.first_unset(), Some(0));
        bs.set(5);
        assert_eq!(bs.first_set(), Some(5));
        bs.clear_all();
        assert_eq!(bs.first_set(), None);
    }

    #[test]
    fn test_set_clear_contains() {
        let mut bs = BS1::new(1);
        assert!(!bs.contains(10));
        bs.set(10);
        assert!(bs.contains(10));
        bs.clear(10);
        assert!(!bs.contains(10));
    }

    #[test]
    fn test_first_set_unset_ge() {
        let mut bs = BS1::new(2);
        // block 0 covers bits 0..64, block 1 covers 64..128
        bs.clear_all();
        bs.set(70);
        assert_eq!(bs.first_set(), Some(70));
        assert_eq!(bs.first_set_ge(0), Some(70));
        assert_eq!(bs.first_set_ge(70), Some(70));
        assert_eq!(bs.first_set_ge(71), None);

        // first_unset should skip bit 70
        assert_eq!(bs.first_unset(), Some(0));
        assert_eq!(bs.first_unset_ge(0), Some(0));
        assert_eq!(bs.first_unset_ge(0).unwrap() != 70, true);
    }

    #[test]
    fn test_union_intersect_difference() {
        let mut a = BS1::new(1);
        let mut b = BS1::new(1);
        a.set(1);
        b.set(2);
        a.union_with(&b);
        assert!(a.contains(1) && a.contains(2));

        a.clear_all();
        a.set(1);
        a.set(2);
        b.clear_all();
        b.set(2);
        a.intersect_with(&b);
        assert!(!a.contains(1) && a.contains(2));

        a.clear_all();
        a.set(1);
        a.set(2);
        b.clear_all();
        b.set(2);
        a.difference_with(&b);
        assert!(a.contains(1) && !a.contains(2));
    }

    #[test]
    fn test_grow_on_set() {
        let mut bs = BS1::new(1);
        assert_eq!(bs.capacity(), usize::BITS as usize);
        bs.set(usize::BITS as usize + 5);
        assert!(bs.contains(usize::BITS as usize + 5));
        assert!(bs.capacity() > usize::BITS as usize);
    }
}
