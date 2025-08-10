#[cfg(test)]
mod tests {
    use pror::fixed_bitset::*;

    #[test]
    fn test_capacity_and_clear() {
        let mut bs = BitSet::new(2);
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
        let mut bs = BitSet::new(1);
        assert!(!bs.contains(10));
        bs.set(10);
        assert!(bs.contains(10));
        bs.clear(10);
        assert!(!bs.contains(10));
    }

    #[test]
    fn test_first_set_unset_ge() {
        let mut bs = BitSet::new(2);
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
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
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
        let mut bs = BitSet::new(1);
        assert_eq!(bs.capacity(), usize::BITS as usize);
        bs.set(usize::BITS as usize + 5);
        assert!(bs.contains(usize::BITS as usize + 5));
        assert!(bs.capacity() > usize::BITS as usize);
    }
}

#[cfg(test)]
mod iter_tests {
    use pror::bitset::BitSetT;
    use pror::fixed_bitset::*;

    #[test]
    fn test_iter_union() {
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
        a.set(1);
        a.set(3);
        a.set(5);
        b.set(2);
        b.set(3);
        b.set(6);
        let u: Vec<_> = a.iter_union(&b).collect();
        assert_eq!(u, vec![1, 2, 3, 5, 6]);
    }

    #[test]
    fn test_iter_intersection() {
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
        a.set(2);
        a.set(4);
        b.set(4);
        b.set(6);
        let i: Vec<_> = a.iter_intersection(&b).collect();
        assert_eq!(i, vec![4]);
    }

    #[test]
    fn test_iter_difference() {
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
        a.set(1);
        a.set(3);
        a.set(5);
        b.set(3);
        b.set(6);
        let d: Vec<_> = a.iter_difference(&b).collect();
        assert_eq!(d, vec![1, 5]);
        let d2: Vec<_> = b.iter_difference(&a).collect();
        assert_eq!(d2, vec![6]);
    }

    #[test]
    fn test_set_between_same_block() {
        let mut bs = BitSet::new(1);
        bs.set_between(5, 20);
        for i in 0..5 {
            assert!(!bs.contains(i), "bit {} should be clear", i);
        }
        for i in 5..20 {
            assert!(bs.contains(i), "bit {} should be set", i);
        }
        assert!(!bs.contains(20), "bit 20 should be clear");
    }

    #[test]
    fn test_set_between_multiple_blocks() {
        let mut bs = BitSet::new(1);
        bs.set_between(10, 75);
        assert!(!bs.contains(9), "bit 9 should be clear");
        for i in 10..75 {
            assert!(bs.contains(i), "bit {} should be set", i);
        }
        assert!(!bs.contains(75), "bit 75 should be clear");
    }

    #[test]
    fn test_set_between_full_block_range() {
        let mut bs = BitSet::new(0);
        bs.set_between(0, usize::BITS as usize);
        for i in 0..(usize::BITS as usize) {
            assert!(bs.contains(i), "bit {} should be set", i);
        }
        assert!(
            !bs.contains(usize::BITS as usize),
            "bit BITS_PER_BLOCK should be clear"
        );
    }

    #[test]
    fn test_first_set() {
        let mut a = BitSet::new(0);
        a.set(0);
        a.set(1);
        a.set(10);
        a.set(63);
        a.set(64);
        a.set(100);
        a.set(12313);
        assert_eq!(a.first_set(), Some(0));
        assert_eq!(a.first_set_ge(1), Some(1));
        assert_eq!(a.first_set_ge(2), Some(10));
        assert_eq!(a.first_set_ge(101), Some(12313));
        assert_eq!(a.first_unset(), Some(2));
        assert_eq!(a.first_unset_ge(64), Some(65));
    }

    #[test]
    fn test_nth() {
        let mut a = BitSet::new(0);
        a.set(0);
        a.set(1);
        a.set(10);
        a.set(63);
        a.set(64);
        a.set(100);
        a.set(12313);
        assert_eq!(a.nth(0), Some(0));
        assert_eq!(a.nth(1), Some(1));
        assert_eq!(a.nth(2), Some(10));
        assert_eq!(a.nth(3), Some(63));
        assert_eq!(a.nth(4), Some(64));
        assert_eq!(a.nth(5), Some(100));
        assert_eq!(a.nth(6), Some(12313));
        assert_eq!(a.nth(7), None);
        assert_eq!(a.nth(8), None);
    }

    #[test]
    fn test_intersect_first_set_basic() {
        let mut a = BitSet::new(2);
        let mut b = BitSet::new(2);
        a.set(3);
        a.set(5);
        a.set(10);
        b.set(2);
        b.set(5);
        b.set(10);
        assert_eq!(a.intersect_first_set(&b), Some(5));
    }

    #[test]
    fn test_intersect_first_set_ge_variations() {
        let mut a = BitSet::new(2);
        let mut b = BitSet::new(2);
        a.set(3);
        a.set(7);
        a.set(15);
        b.set(7);
        b.set(20);

        // First common ≥ 0 is 7
        assert_eq!(a.intersect_first_set_ge(&b, 0), Some(7));

        // No common ≥ 8
        assert_eq!(a.intersect_first_set_ge(&b, 8), None);

        // ge exactly at a common bit
        assert_eq!(a.intersect_first_set_ge(&b, 7), Some(7));

        // ge at 15: a has 15, b.next is 20 → no intersection
        assert_eq!(a.intersect_first_set_ge(&b, 15), None);
    }

    #[test]
    fn test_no_intersection_and_empty() {
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
        a.set(1);
        a.set(4);
        b.set(2);
        b.set(5);
        assert_eq!(a.intersect_first_set(&b), None);

        let empty_a = BitSet::new(1);
        let empty_b = BitSet::new(1);
        assert_eq!(empty_a.intersect_first_set(&empty_b), None);
    }

    #[test]
    fn test_intersect_at_ge_edge() {
        let mut a = BitSet::new(1);
        let mut b = BitSet::new(1);
        a.set(8);
        b.set(8);

        // exact edge match
        assert_eq!(a.intersect_first_set_ge(&b, 8), Some(8));

        // beyond edge → none
        assert_eq!(a.intersect_first_set_ge(&b, 9), None);
    }
}
