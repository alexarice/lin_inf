use crate::Node;
use std::collections::HashSet;

pub trait MClique {
    fn mc_from_set(set: &HashSet<Node>) -> Self;
    fn mc_contains(&self, x: Node) -> bool;
    fn mc_subset(&self, x: &Self) -> bool;
    fn mc_remove(&self, x: Node) -> Self;
}

macro_rules! impl_mc {
    ( $t : ty ) => {
        impl MClique for $t {
            fn mc_from_set(set: &HashSet<Node>) -> Self {
                set.iter().map(|n| 1 << n).sum()
            }
            fn mc_contains(&self, x: Node) -> bool {
                *self & 1 << x != 0
            }
            fn mc_subset(&self, x: &Self) -> bool {
                x | self == *x
            }
            fn mc_remove(&self, x: Node) -> Self {
                self & (<$t>::MAX - (1 << x))
            }
        }
    };
}

impl_mc!(u8);
impl_mc!(u16);

impl MClique for HashSet<Node> {
    fn mc_from_set(set: &Self) -> Self {
        set.clone()
    }
    fn mc_contains(&self, x: Node) -> bool {
        self.contains(&x)
    }
    fn mc_subset(&self, x: &Self) -> bool {
        self.is_subset(x)
    }
    fn mc_remove(&self, x: Node) -> Self {
        let mut r = self.clone();
        r.remove(&x);
        r
    }
}

pub fn linear_implication<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>) -> bool {
    mc1.iter().all(|p| mc2.iter().any(|q| q.mc_subset(p)))
}

pub fn is_trivial_at<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>, x: Node) -> bool {
    mc1.iter().all(|p| {
        let pr = p.mc_remove(x);
        mc2.iter().any(|q| q.mc_subset(&pr))
    })
}

pub fn is_trivial<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>, number_vars: usize) -> bool {
    (0..number_vars).any(|x| is_trivial_at(mc1, mc2, x))
}
