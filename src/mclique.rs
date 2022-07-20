//! Data types and functions for representing maximum cliques of graphs

use crate::Node;
use std::collections::HashSet;

/// Trait acting as a wrapper around set like structures exposing the functions needed for representing a maximum clique of a graph.
pub trait MClique {
    /// A maximum clique is a set of nodes and can be build from a [`HashSet`].
    fn mc_from_set(set: &HashSet<Node>) -> Self;
    /// Check if a node is contained in a maximum clique.
    fn mc_contains(&self, x: Node) -> bool;
    /// Check if a maximum clique is a subset of another maximum clique `x`.
    fn mc_subset(&self, x: &Self) -> bool;
    /// Remove a node `x` from a maximum clique.
    fn mc_remove(&self, x: Node) -> Self;
}

macro_rules! impl_mc {
    ( $t : ty ) => {
	/// Numerical implementation of MClique which uses each bit to store whether a node is in the set.
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

/// Implementation of MClique acting as a wrapper around [`HashSet`].
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

/// Determine whether formula represented by a graph with maximum cliques `mc1` implies a formula represented by a graph with maximum cliques `mc2`.
pub fn linear_implication<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>) -> bool {
    mc1.iter().all(|p| mc2.iter().any(|q| q.mc_subset(p)))
}

/// Determine whether an implication between formulae represented by graphs with max cliques `mc1` and `mc2` is trivial at node `x`.
pub fn is_trivial_at<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>, x: Node) -> bool {
    mc1.iter().all(|p| {
        let pr = p.mc_remove(x);
        mc2.iter().any(|q| q.mc_subset(&pr))
    })
}

/// Determine whether an implication between formulae represented by graphs of size `number_vars` with max cliques `mc1` and `mc2` is trivial at any node.
pub fn is_trivial<T: MClique>(mc1: &Vec<T>, mc2: &Vec<T>, number_vars: usize) -> bool {
    (0..number_vars).any(|x| is_trivial_at(mc1, mc2, x))
}
