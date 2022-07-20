//! Data type and function for working with permutations of graphs.

use crate::Node;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

/// Type representing permutations of the nodes in a graph.
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub struct Permutation(Vec<Node>);

impl Permutation {
    /// Returns the size of the permutation.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Applies a permutation to a node to get another node.
    pub fn ap(&self, ix: Node) -> Node {
        if ix >= self.len() {
            ix
        } else {
            self.0[ix]
        }
    }

    /// Get all permutations of size `number_vars`.
    pub fn get_all(number_vars: usize) -> impl Iterator<Item = Self> {
        (0..number_vars)
            .permutations(number_vars)
            .map(|x| Permutation(x))
    }

    /// Obtain the inverse permutation.
    pub fn invert(&self) -> Permutation {
        let mut new = vec![0; self.len()];
        for x in 0..self.len() {
            new[self.ap(x)] = x;
        }
        Permutation(new)
    }

    /// Returns the identity permutation on `number_vars`.
    pub fn id(number_vars: usize) -> Self {
        Permutation((0..number_vars).collect())
    }

    /// Compose two permutations.
    pub fn after(&self, other: &Permutation) -> Permutation {
        Permutation((0..other.len()).map(|x| self.ap(other.ap(x))).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use quickcheck::{Arbitrary, Gen};
    use rand::Rng;

    impl Arbitrary for Permutation {
        fn arbitrary<G: Gen>(g: &mut G) -> Permutation {
            let len = Permutation::get_all(8).count();
            let mut perms = Permutation::get_all(8);

            perms.nth(g.gen_range(0, len)).unwrap()
        }
    }

    #[quickcheck]
    fn comp_test(p1: Permutation, p2: Permutation) {
        for x in 0..8 {
            assert_eq!(p1.after(&p2).ap(x), p1.ap(p2.ap(x)));
        }
    }

    #[quickcheck]
    fn unit_left(p: Permutation) {
        assert_eq!(p, Permutation::id(8).after(&p))
    }

    #[quickcheck]
    fn unit_right(p: Permutation) {
        assert_eq!(p, p.after(&Permutation::id(8)))
    }

    #[quickcheck]
    fn inv_left(p: Permutation) {
        assert_eq!(Permutation::id(8), p.invert().after(&p))
    }

    #[quickcheck]
    fn inv_right(p: Permutation) {
        assert_eq!(Permutation::id(8), p.after(&p.invert()))
    }

    #[quickcheck]
    fn inv_involution(p: Permutation) {
        assert_eq!(p, p.invert().invert())
    }
}
