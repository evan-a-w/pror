use std::cmp::max;
use std::fmt::Write;

struct Node<K, V> {
    key: K,
    value: V,
    height: usize,
    left: Option<usize>,
    right: Option<usize>,
}

enum KeyOrIdx<K> {
    Key(K),
    Index(usize),
}

struct NodePool<K, V> {
    nodes: Vec<Node<K, V>>,
    free_list: Vec<usize>,
}

impl<K, V> NodePool<K, V> {
    fn new() -> Self {
        NodePool {
            nodes: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn alloc(&mut self, key: K, value: V) -> usize {
        if let Some(idx) = self.free_list.pop() {
            self.nodes[idx] = Node {
                key,
                value,
                height: 1,
                left: None,
                right: None,
            };
            idx
        } else {
            let idx = self.nodes.len();
            self.nodes.push(Node {
                key,
                value,
                height: 1,
                left: None,
                right: None,
            });
            idx
        }
    }

    fn free(&mut self, idx: usize) {
        self.free_list.push(idx);
    }
}

pub struct AvlTree<K: Ord + Clone, V: Clone> {
    pool: NodePool<K, V>,
    root: Option<usize>,
}

impl<K: Ord + Clone, V: Clone> AvlTree<K, V> {
    pub fn new() -> Self {
        AvlTree {
            pool: NodePool::new(),
            root: None,
        }
    }

    fn height_of(&self, idx: Option<usize>) -> usize {
        idx.map_or(0, |i| self.pool.nodes[i].height)
    }

    fn update_height(&mut self, idx: usize) {
        let lh = self.height_of(self.pool.nodes[idx].left);
        let rh = self.height_of(self.pool.nodes[idx].right);
        self.pool.nodes[idx].height = max(lh, rh) + 1;
    }

    fn balance_factor(&self, idx: usize) -> isize {
        let lh = self.height_of(self.pool.nodes[idx].left) as isize;
        let rh = self.height_of(self.pool.nodes[idx].right) as isize;
        lh - rh
    }

    fn rotate_right(&mut self, y: usize) -> usize {
        let x = self.pool.nodes[y].left.expect("rotate_right on None");
        let t2 = self.pool.nodes[x].right;
        self.pool.nodes[x].right = Some(y);
        self.pool.nodes[y].left = t2;
        self.update_height(y);
        self.update_height(x);
        x
    }

    fn rotate_left(&mut self, x: usize) -> usize {
        let y = self.pool.nodes[x].right.expect("rotate_left on None");
        let t2 = self.pool.nodes[y].left;
        self.pool.nodes[y].left = Some(x);
        self.pool.nodes[x].right = t2;
        self.update_height(x);
        self.update_height(y);
        y
    }

    fn rebalance(&mut self, idx: usize) -> usize {
        self.update_height(idx);
        let bf = self.balance_factor(idx);
        if bf > 1 {
            if self.balance_factor(self.pool.nodes[idx].left.unwrap()) < 0 {
                let l = self.pool.nodes[idx].left.unwrap();
                self.pool.nodes[idx].left = Some(self.rotate_left(l));
            }
            return self.rotate_right(idx);
        }
        if bf < -1 {
            if self.balance_factor(self.pool.nodes[idx].right.unwrap()) > 0 {
                let r = self.pool.nodes[idx].right.unwrap();
                self.pool.nodes[idx].right = Some(self.rotate_right(r));
            }
            return self.rotate_left(idx);
        }
        idx
    }

    fn insert_node(&mut self, idx: Option<usize>, key: K, value: V) -> usize {
        if let Some(i) = idx {
            if key < self.pool.nodes[i].key {
                let l = self.insert_node(self.pool.nodes[i].left, key, value);
                self.pool.nodes[i].left = Some(l);
            } else if key > self.pool.nodes[i].key {
                let r = self.insert_node(self.pool.nodes[i].right, key, value);
                self.pool.nodes[i].right = Some(r);
            } else {
                self.pool.nodes[i].value = value;
            }
            self.rebalance(i)
        } else {
            self.pool.alloc(key, value)
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        let r = self.insert_node(self.root, key, value);
        self.root = Some(r);
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let mut cur = self.root;
        while let Some(i) = cur {
            if key < &self.pool.nodes[i].key {
                cur = self.pool.nodes[i].left;
            } else if key > &self.pool.nodes[i].key {
                cur = self.pool.nodes[i].right;
            } else {
                return Some(&self.pool.nodes[i].value);
            }
        }
        None
    }

    fn min_value_node(&self, mut idx: usize) -> usize {
        while let Some(l) = self.pool.nodes[idx].left {
            idx = l;
        }
        idx
    }

    fn delete_node(&mut self, idx: Option<usize>, key: KeyOrIdx<&K>) -> Option<usize> {
        if let Some(i) = idx {
            let cmp = match key {
                KeyOrIdx::Key(k) => k.cmp(&self.pool.nodes[i].key),
                KeyOrIdx::Index(idx) => self.pool.nodes[idx.clone()]
                    .key
                    .cmp(&self.pool.nodes[i].key),
            };
            match cmp {
                std::cmp::Ordering::Less => {
                    self.pool.nodes[i].left = self.delete_node(self.pool.nodes[i].left, key)
                }
                std::cmp::Ordering::Greater => {
                    self.pool.nodes[i].right = self.delete_node(self.pool.nodes[i].right, key)
                }
                std::cmp::Ordering::Equal => {
                    if self.pool.nodes[i].left.is_none() {
                        let r = self.pool.nodes[i].right;
                        self.pool.free(i);
                        return r;
                    } else if self.pool.nodes[i].right.is_none() {
                        let l = self.pool.nodes[i].left;
                        self.pool.free(i);
                        return l;
                    } else {
                        let succ = self.min_value_node(self.pool.nodes[i].right.unwrap());
                        let (li, ri) = if i == succ {
                            self.pool.free(i);
                            return None;
                        } else if i > succ {
                            (succ, i)
                        } else {
                            (i, succ)
                        };
                        let (l, r) = self.pool.nodes.split_at_mut(ri);
                        std::mem::swap(&mut l[li].key, &mut r[0].key);
                        std::mem::swap(&mut l[li].value, &mut r[0].value);
                        self.pool.nodes[i].right =
                            self.delete_node(self.pool.nodes[i].right, KeyOrIdx::Index(succ));
                    }
                }
            };
            Some(self.rebalance(i))
        } else {
            None
        }
    }

    pub fn remove(&mut self, key: &K) {
        self.root = self.delete_node(self.root, KeyOrIdx::Key(key));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::max;

    use expect_test::{expect, Expect};

    fn inorder_keys<K: Ord + Clone, V: Clone>(tree: &AvlTree<K, V>) -> Vec<K> {
        fn traverse<K: Clone, V: Clone>(
            idx: Option<usize>,
            pool: &NodePool<K, V>,
            out: &mut Vec<K>,
        ) {
            if let Some(i) = idx {
                traverse(pool.nodes[i].left, pool, out);
                out.push(pool.nodes[i].key.clone());
                traverse(pool.nodes[i].right, pool, out);
            }
        }
        let mut keys = Vec::new();
        traverse(tree.root, &tree.pool, &mut keys);
        keys
    }

    fn inorder_iter<K: Ord + Clone, V: Clone, F: Fn(usize, &K, &V) -> ()>(
        tree: &AvlTree<K, V>,
        f: &F,
    ) {
        fn traverse<K: Clone, V: Clone, F: Fn(usize, &K, &V) -> ()>(
            idx: Option<usize>,
            level: usize,
            pool: &NodePool<K, V>,
            f: &F,
        ) {
            if let Some(i) = idx {
                traverse(pool.nodes[i].left, level + 1, pool, f);
                f(level, &pool.nodes[i].key, &pool.nodes[i].value);
                traverse(pool.nodes[i].right, level + 1, pool, f);
            }
        }
        traverse(tree.root, 0, &tree.pool, f);
    }

    fn pretty_print<K: Ord + Clone + std::fmt::Display, V: Clone + std::fmt::Display>(
        tree: &AvlTree<K, V>,
    ) {
        inorder_iter(tree, &|level, key, value| {
            println!("{}{}: {}", "  ".repeat(level), key, value);
        });
    }
    fn pretty_print_to_string<K, V>(tree: &AvlTree<K, V>) -> String
    where
        K: Ord + Clone + std::fmt::Display,
        V: Clone + std::fmt::Display,
    {
        fn traverse<K: Clone + std::fmt::Display, V: Clone + std::fmt::Display>(
            idx: Option<usize>,
            level: usize,
            pool: &NodePool<K, V>,
            mut out: String,
        ) -> String {
            if let Some(i) = idx {
                out = traverse(pool.nodes[i].left, level + 1, pool, out);
                writeln!(
                    &mut out,
                    "{}{}: {}",
                    "  ".repeat(level),
                    &pool.nodes[i].key,
                    &pool.nodes[i].value
                )
                .expect("writing to String cannot fail");
                out = traverse(pool.nodes[i].right, level + 1, pool, out);
            }
            out
        }
        traverse(tree.root, 0, &tree.pool, String::new())
    }

    fn check_balance<K: Clone, V: Clone>(
        idx: Option<usize>,
        pool: &NodePool<K, V>,
    ) -> (bool, usize) {
        if let Some(i) = idx {
            let (lb, lh) = check_balance(pool.nodes[i].left, pool);
            let (rb, rh) = check_balance(pool.nodes[i].right, pool);
            let balanced = lb && rb && ((lh as isize - rh as isize).abs() <= 1);
            (balanced, max(lh, rh) + 1)
        } else {
            (true, 0)
        }
    }

    #[test]
    fn test_insert_and_get() {
        let mut tree = AvlTree::new();
        tree.insert("a", 1);
        tree.insert("b", 2);
        tree.insert("c", 3);
        let s = pretty_print_to_string(&tree);
        let expect = expect![[r#"
              a: 1
            b: 2
              c: 3
        "#]];
        expect.assert_eq(&s);
        assert_eq!(tree.get(&"a"), Some(&1));
        assert_eq!(tree.get(&"b"), Some(&2));
        assert_eq!(tree.get(&"c"), Some(&3));
    }

    #[test]
    fn test_update_value() {
        let mut tree = AvlTree::new();
        tree.insert("key", 10);
        assert_eq!(tree.get(&"key"), Some(&10));
        tree.insert("key", 20);
        assert_eq!(tree.get(&"key"), Some(&20));
    }

    #[test]
    fn test_inorder_sorted() {
        let mut tree = AvlTree::new();
        let vals = vec![10, 5, 20, 15, 25, 3, 8];
        for &v in &vals {
            tree.insert(v, v * 10);
        }
        let mut keys = inorder_keys(&tree);
        let mut sorted = vals.clone();
        sorted.sort();
        assert_eq!(keys, sorted);
    }

    #[test]
    fn test_remove_leaf() {
        let mut tree = AvlTree::new();
        tree.insert(1, "one");
        tree.insert(2, "two");
        let s = pretty_print_to_string(&tree);
        let expect = expect![[r#"
            1: one
              2: two
        "#]];
        expect.assert_eq(&s);
        tree.remove(&2);
        let s = pretty_print_to_string(&tree);
        let expect = expect![[r#"
            1: one
        "#]];
        expect.assert_eq(&s);
        assert_eq!(tree.get(&2), None);
        assert_eq!(tree.get(&1), Some(&"one"));
    }

    #[test]
    fn test_remove_node_with_one_child() {
        let mut tree = AvlTree::new();
        tree.insert(10, "ten");
        tree.insert(5, "five");
        tree.insert(3, "three");
        tree.remove(&5);
        assert_eq!(tree.get(&5), None);
        assert_eq!(tree.get(&3), Some(&"three"));
        assert_eq!(tree.get(&10), Some(&"ten"));
    }

    #[test]
    fn test_remove_node_with_two_children() {
        let mut tree = AvlTree::new();
        for &k in &[2, 1, 3] {
            tree.insert(k, k);
        }
        tree.remove(&2);
        assert_eq!(tree.get(&2), None);
        let keys = inorder_keys(&tree);
        assert_eq!(keys, vec![1, 3]);
    }

    #[test]
    fn test_balance_after_operations() {
        let mut tree = AvlTree::new();
        for k in 1..=100 {
            tree.insert(k, k);
        }
        for k in &[50, 75, 25] {
            tree.remove(k);
        }
        let (balanced, _) = check_balance(tree.root, &tree.pool);
        assert!(balanced, "Tree is unbalanced after operations");
    }
}
