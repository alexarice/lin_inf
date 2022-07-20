//! Tools for working with undirected graphs and their relation to formulae

use crate::formula::*;
use crate::mclique::MClique;
use crate::permutation::Permutation;
use crate::Node;
use itertools::{Either, Itertools,concat};
use rayon::prelude::*;
use std::collections::HashSet;

fn partitions<T>(s: &[T]) -> Vec<(Vec<T>, Vec<T>)>
where
    T: Clone,
{
    (0..2usize.pow(s.len() as u32))
        .map(|i| {
            s.iter().enumerate().partition_map(|(t, element)| {
                if (i >> t) % 2 == 1 {
                    Either::Left(element.clone())
                } else {
                    Either::Right(element.clone())
                }
            })
        })
        .collect()
}


/// Functions for working with graphs
///
/// Implementing this trait allows the type to act as an undirected graph, and equips it with functions for working with graphs and their relation to linear inferences.
/// Note that graphs defined with this trait do not know their size and many of the functions require this size to be passed in. This is done to save memory space when working with large numbers of graphs.
pub trait LinGraph: Sized + Eq + Send {
    /// Test whether there is an edge between nodes `x` and `y`
    /// Returns true if here is an edge between `x` and `y` and false otherwise.
    /// Note that this should return for all `x` and `y`, even if `x` and `y` are larger than the intended size of the graph
    fn get(&self, x: Node, y: Node) -> bool;

    /// Build a graph of size `number_vars` from a function `f` describing the edge data.
    ///
    /// For all `x` and `y` less than `number_vars` we should have:
    /// ```
    /// !assert_eq(build(f,number_vars).get(x,y),f(x,y))
    /// ```
    /// and if `x` or `y` are greater than or equal to `number_vars` then we should have:
    /// ```
    /// !assert_eq(build(f,number-vars).get(x,y), false)
    /// ```
    fn build<T>(f: T, number_vars: usize) -> Self
    where
        T: Fn(Node, Node) -> bool;

    /// Decides if a graph is P4 free
    ///
    /// Returns true if none of the induced subgraphs of the input graph are isomorphic to P4
    fn p4_free(&self, number_vars: usize) -> bool {
        (0..number_vars).permutations(4).all(|v| {
            let (a, b, c, d) = v.into_iter().collect_tuple().unwrap();
            !(self.get(a, b)
                && !(self.get(a, c))
                && !(self.get(a, d))
                && self.get(b, c)
                && !(self.get(b, d))
                && self.get(c, d))
        })
    }
    /// Returns all possible extensions of a `number_vars` sized graph to a `number_vars + 1` sized graph.
    fn all_extensions(&self, number_vars: usize) -> Vec<Self>;

    /// Returns all P4 free graphs of size `number_vars`.
    fn all_p4_free(number_vars: usize) -> Vec<Self> {
	let reduced_p4 = |x: &Self| {
            (0..number_vars - 1).permutations(3).all(|v| {
                let (a, b, c) = v.into_iter().collect_tuple().unwrap();
                !(x.get(number_vars - 1, a)
                  && !(x.get(number_vars - 1, b))
                  && !(x.get(number_vars - 1, c))
                  && x.get(a, b)
                  && !(x.get(a, c))
                  && x.get(b, c))
                    && !(x.get(a, number_vars - 1)
                         && !(x.get(a, b))
                         && !(x.get(a, c))
                         && x.get(number_vars - 1, b)
                         && !(x.get(number_vars - 1, c))
                         && x.get(b, c))
            })
        };
        match number_vars {
            0 => {
                vec![Self::build(|_,_| false, 0)]
            }
            _ => {
                let m = number_vars - 1;
                let p4_free = Self::all_p4_free(m);
                let new_graphs = p4_free
                    .into_iter()
		    .flat_map(|x| x.all_extensions(m));
                new_graphs.par_bridge().filter(|x| reduced_p4(x)).collect()
            }
        }
    }

    /// Returns all graphs of size `number_vars`
    fn all_graphs(number_vars: usize) -> Vec<Self>;

    /// Finds all nodes adjacent to node `x` in the given graph of size `number_vars`
    fn neighbours(&self, number_vars: usize, x: Node) -> HashSet<Node> {
        (0..number_vars).filter(|&m| self.get(x, m)).collect()
    }

    /// Apply a permutation to a graph to obtain a new graph.
    fn apply_perm(&self, p: &Permutation) -> Self {
        let pinv = p.invert();
        Self::build(|x, y| self.get(pinv.ap(x), pinv.ap(y)), p.len())
    }

    /// Fully dualise a graph of size `number_vars` (invert every edge to a non edge and every non edge to an edge)
    fn dualise(&self, number_vars: usize) -> Self {
	Self::build(|x, y| !self.get(x,y), number_vars)
    }

    /// Return all max cliques of a graph
    fn max_cliques<M: MClique>(&self, number_vars: usize) -> Vec<M> {
        fn bron_kerbosch<T: LinGraph>(
            lg: &T,
            number_vars: usize,
            r: HashSet<Node>,
            inp: HashSet<Node>,
            inx: HashSet<Node>,
            cliques: &mut Vec<HashSet<Node>>,
        ) {
            let mut p = inp;
            let mut x = inx;
            if p.is_empty() && x.is_empty() {
                cliques.push(r.clone())
            }
            for v in p.clone() {
                bron_kerbosch(
                    lg,
                    number_vars,
                    r.union(&vec![v].into_iter().collect()).cloned().collect(),
                    p.intersection(&lg.neighbours(number_vars, v))
                        .cloned()
                        .collect(),
                    x.intersection(&lg.neighbours(number_vars, v))
                        .cloned()
                        .collect(),
                    cliques,
                );
                p.remove(&v);
                x.insert(v);
            }
        }
        let mut cliques: Vec<HashSet<Node>> = Vec::new();
        bron_kerbosch(
            self,
            number_vars,
            HashSet::new(),
            (0..number_vars).collect(),
            HashSet::new(),
            &mut cliques,
        );
        cliques.iter().map(|x| M::mc_from_set(x)).collect()
    }

    /// Determines whether a graph is the join of the induced subgraphs with vertices `a` and `b`.
    fn is_and_partition(&self, a: &Vec<Node>, b: &Vec<Node>) -> bool {
        a.iter().all(|&x| b.iter().all(|&y| self.get(x, y)))
    }

    /// Determines whether a graph is the disjoint union of the induced subgraphs with vertices `a` and `b`.
    fn is_or_partition(&self, a: &Vec<Node>, b: &Vec<Node>) -> bool {
        a.iter().all(|&x| b.iter().all(|&y| !self.get(x, y)))
    }

    /// Finds the cograph decomposition of a P4-free graph of size `number_vars`, returning a formula.
    /// This function does not check that the graph is P4-free, and will fail if it is not.
    fn cograph_decomp(&self, number_vars: usize) -> Formula {
        fn helper<T: LinGraph>(s: &T, xs: Vec<Node>) -> Formula {
            if xs.len() == 1 {
                return Var(xs[0]);
            }

            partitions(&xs)
                .into_iter()
                .filter_map(|(ys, zs)| {
                    if ys.len() > 0 && zs.len() > 0 {
                        if s.is_and_partition(&ys, &zs) {
                            Some(helper(s, ys).and(helper(s, zs)))
                        } else if s.is_or_partition(&ys, &zs) {
                            Some(helper(s, ys).or(helper(s, zs)))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .next()
                .expect("Graph was not p4 free")
        }
        helper(self, (0..number_vars).collect())
    }

    /// Builds a graph from a formula `f`.
    fn from_formula(f: &Formula) -> Self {
        Self::build(|x, y| f.least_common_connective(x, y) == Some(And), f.len())
    }

    /// Counts number of edges.
    fn edges(&self, number_vars : usize) -> usize {
	let mut count = 0;
	for x in 0..number_vars {
	    for y in x + 1 .. number_vars {
		if self.get(x,y) {count += 1;}
	    }
	}
	count
    }

    /// Counts number of non-edges.
    fn non_edges(&self, number_vars : usize) -> usize {
	let mut count = 0;
	for x in 0..number_vars {
	    for y in x + 1 .. number_vars {
		if ! self.get(x,y) {count += 1;}
	    }
	}
	count
    }
}

fn calc_bit(x: Node, y: Node) -> usize {
    (1..y).sum::<usize>() + x
}

macro_rules! impl_lg {
    ( $x : ty ) => {
        impl LinGraph for $x {
	    /// Numeric implementation of graphs which stores the presense of each edge as a bit in the integer.
	    /// This allows for efficient memory usage and gives a natural ordering to graphs.
            fn get(&self, x: Node, y: Node) -> bool {
                if x == y {
                    false
                } else if x > y {
                    self.get(y, x)
                } else {
                    *self & 1 << calc_bit(x, y) != 0
                }
            }
	    fn all_extensions(&self, number_vars : usize) -> Vec<Self> {
		(0..((2 as $x).pow(number_vars as u32))).map(|x| *self + (x << (0..(number_vars as $x)).sum::<$x>())).collect()
	    }
	    fn all_graphs(n: usize) -> Vec<$x> {
		(0..(2 as $x).pow((0..n as u32).sum())).collect()
	    }
            fn build<T>(f: T, number_vars: usize) -> Self
            where
                T: Fn(Node, Node) -> bool,
            {
                let mut sum = 0;
                for (x, y) in (0..number_vars).tuple_combinations() {
                    sum += if f(x, y) { 1 << calc_bit(x, y) } else { 0 };
                }
                sum
            }
        }
    };
}

impl_lg!(u8);
impl_lg!(u16);
impl_lg!(u32);
impl_lg!(u64);
impl_lg!(usize);
impl_lg!(u128);

impl LinGraph for Vec<bool> {
    /// Simple unbounded implementation of graphs as a vector of booleans, with each boolean representing the data for one edge.
    fn get(&self, x: Node, y: Node) -> bool {
        if x == y {
            false
        } else if x > y {
            self.get(y, x)
        } else {
            let b = calc_bit(x, y);
            b < self.len() && self[calc_bit(x, y)]
        }
    }
    fn all_extensions(&self, number_vars : usize) -> Vec<Self> {
	[false,true].iter().cloned().combinations_with_replacement(number_vars).map(move |mut x| {
	    let mut r = self.clone();
	    r.append(&mut x);
	    r
	}).collect()
    }
    fn all_graphs(n: usize) -> Vec<Self> {
	[false,true].iter().cloned().combinations_with_replacement((0..n).sum()).collect()
    }
    fn build<T>(f: T, number_vars: usize) -> Self
    where
        T: Fn(Node, Node) -> bool,
    {
        let mut r = vec![];
        for j in 1..number_vars {
            for i in 0..j {
                r.push(f(i, j));
            }
        }
        r
    }
}

/// Given graphs `p` and `q` of size `number_vars`, determine whether `p` can be reduced to `q` using only the medial reduction.
pub fn is_medial_star<T: LinGraph>(p: &T, q: &T, number_vars: usize) -> bool {
    let pairs = || (0..number_vars).cartesian_product(0..number_vars);
    let cond1 = pairs().all(|(a, b)| !p.get(a, b) || q.get(a, b));

    let psquare = |a, b, c, d| {
        p.get(a, b) && p.get(c, d) && !p.get(a, c) && !p.get(a, d) && !p.get(b, c) && !p.get(b, d)
    };
    let qsquare = |a, b, c, d| {
        q.get(a, b) && q.get(c, d) && !q.get(a, c) && q.get(a, d) && q.get(b, c) && !q.get(b, d)
    };
    let cond2 = pairs().all(|(a, d)| {
        a == d
            || p.get(a, d)
            || !q.get(a, d)
            || pairs().any(|(b, c)| psquare(a, b, c, d) && qsquare(a, b, c, d))
    });
    cond1 && cond2
}

fn is_internally_unchanged<T: LinGraph>(lg1: &T, lg2: &T, xs: &Vec<Node>) -> bool {
    xs.iter()
        .all(|&x| xs.iter().all(|&y| lg1.get(x, y) == lg2.get(x, y)))
}

fn is_switch_help<T: LinGraph>(lg1: &T, lg2: &T, xs: &Vec<Node>) -> bool {
    let cond1 = |a: &Vec<Node>, b: &Vec<Node>| {
        lg1.is_and_partition(a, b)
            && lg2.is_and_partition(a, b)
            && is_internally_unchanged(lg1, lg2, a)
            && is_switch_help(lg1, lg2, b)
    };

    let cond2 = |a: &Vec<Node>, b: &Vec<Node>| {
        lg1.is_or_partition(a, b)
            && lg2.is_or_partition(a, b)
            && is_internally_unchanged(lg1, lg2, a)
            && is_switch_help(lg1, lg2, b)
    };

    let cond3 = |a: &Vec<Node>, b: &Vec<Node>| {
        partitions(&b[..]).iter().any(|(c, d)| {
            c.len() > 0
                && d.len() > 0
                && [a, c, d]
                    .iter()
                    .all(|x| is_internally_unchanged(lg1, lg2, x))
                && lg1.is_and_partition(a, b)
                && lg1.is_or_partition(c, d)
                && lg2.is_or_partition(&[&a[..], &c[..]].concat(), d)
                && lg2.is_and_partition(a, c)
        })
    };

    let conditions = |a, b| cond1(a, b) || cond2(a, b) || cond3(a, b);
    partitions(&xs[..])
        .iter()
        .any(|(a, b)| a.len() > 0 && b.len() > 0 && conditions(a, b))
}

/// Determine whether `lg1` reduces to `lg2` (both of which have size `number_vars`) by a single application of switch.
pub fn is_switch<T: LinGraph>(lg1: &T, lg2: &T, number_vars: usize) -> bool {
    is_switch_help(lg1, lg2, &(0..number_vars).collect())
}

/// Determines whether the sets of vertices `xs` and `ys` partitions the graph `lg` into two modules.
pub fn is_module<T: LinGraph>(lg: &T, xs:&Vec<Node>, ys:& Vec<Node>) -> bool {
    ys.iter().all(|y|{
	let mut vs : Vec<_> = xs.iter().map(|x| lg.get(*x, *y)).collect();
	vs.dedup();
	vs.len() <= 1
    })
}

/// Takes an inference of size `number_vars` and returns the least inference that can be obtained by applying a permutation to both the `premise` and `conclusion`.
/// The returned inference is least with respect to a lexicographic ordering on first the premise and then the conclusion, based off the given ordering of graphs.
pub fn reduce_inference<T: LinGraph + Ord>(premise: T, conclusion: T, number_vars: usize) -> (T,T) {
    Permutation::get_all(number_vars)
	.map(|p| (premise.apply_perm(&p),conclusion.apply_perm(&p)))
        .min_by(|(a,b), (c,d)| {
	    a.cmp(c).then(b.cmp(d))
	})
        .unwrap()
}

fn all_ne_partitions<T: LinGraph>(s : &[usize], lhs: &T, rhs: &T, parts: usize) -> Vec<Vec<Vec<usize>>> {

    if s.len() < parts {
	return vec![];
    }
    if parts <= 1 {
	return vec![vec![s.to_vec()]];
    }
    concat(partitions(s).into_iter().filter(|(a,b)| a.len() > 0 && is_module(lhs, a, b) && is_module(rhs, a, b)).map(|(a,b)| {
	all_ne_partitions(&b, lhs, rhs, parts - 1).into_iter().map(|mut v| {v.push(a.clone()); v}).collect()
    }).collect::<Vec<_>>())
}

fn is_rewrite_help<T: LinGraph, U: LinGraph>(lg1: &T, lg2: &T, xs: &Vec<Node>, lhs: &U, rhs: &U, n_vars_rule: usize) -> bool {
    let c = all_ne_partitions(xs, lg1, lg2, n_vars_rule).iter().any(|vs| {
	let b = vs.iter().all(|v| !v.is_empty() && is_internally_unchanged(lg1, lg2, v));
	let b2 = (0..n_vars_rule).cartesian_product(0..n_vars_rule).filter(|(x,y)| x != y).all(|(x,y)| {
	    let cond1 = if lhs.get(x,y) {
		lg1.is_and_partition(&vs[x], &vs[y])
	    } else {
		lg1.is_or_partition(&vs[x], &vs[y])
	    };
	    let cond2 = if rhs.get(x,y) {
		lg2.is_and_partition(&vs[x], &vs[y])
	    } else {
		lg2.is_or_partition(&vs[x], &vs[y])
	    };
	    cond1 && cond2
	});
	b && b2
    });
    c
}

/// Determines whether `lg1` can be rewritten to `lg2` (both of size `n_vars`) by rule `lg1` -> `lg2` (both of size `n_vars_rule`).
pub fn is_rewrite<T: LinGraph, U: LinGraph>(lg1 : &T, lg2: &T, lhs : &U, rhs: &U, n_vars: usize, n_vars_rule: usize) -> bool {
    partitions(&(0..n_vars).collect::<Vec<_>>()).iter().any(|(a,b)| {
	is_module(lg1,a,b) &&
	    is_module(lg2,a,b) &&
	    is_rewrite_help(lg1, lg2, a, lhs, rhs, n_vars_rule)
    })
}

/// Counts times a non-edge becomes an edge in an inference
pub fn non_edge_to_edge<T: LinGraph>(lg1 : &T, lg2 : &T, number_vars: usize) -> usize {
    let mut count = 0;
    for x in 0..number_vars {
	for y in x + 1 .. number_vars {
	    if !lg1.get(x,y) && lg2.get(x,y) {count += 1;}
	}
    }
    count
}

/// Counts times an edge becomes a non-edge in an inference
pub fn edge_to_non_edge<T: LinGraph>(lg1 : &T, lg2 : &T, number_vars: usize) -> usize {
    let mut count = 0;
    for x in 0..number_vars {
	for y in x + 1 .. number_vars {
	    if lg1.get(x,y) && !lg2.get(x,y) {count += 1;}
	}
    }
    count
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::mclique::*;

    lazy_static! {
        static ref SWITCH1: u32 = u32::from_formula(&Var(0).and(Var(1).or(Var(2))));
        static ref SWITCH2: u32 = u32::from_formula(&(Var(0).and(Var(1))).or(Var(2)));
        static ref SW1MC: Vec<u8> = SWITCH1.max_cliques(3);
	static ref SW2MC: Vec<u8> = SWITCH2.max_cliques(3);
	static ref SWITCH1EX: u32 = u32::from_formula(&(Var(0).and(Var(1).or(Var(2)))).and(Var(3)));
	static ref SWITCH2EX: u32 = u32::from_formula(&((Var(0).and(Var(1))).or(Var(2))).and(Var(3)));
        static ref MEDIAL1: u32 = u32::from_formula(&(Var(0).and(Var(1))).or(Var(2).and(Var(3))));
        static ref MEDIAL2: u32 = u32::from_formula(&(Var(0).or(Var(2))).and(Var(1).or(Var(3))));
        static ref M1MC: Vec<u8> = MEDIAL1.max_cliques(4);
        static ref M2MC: Vec<u8> = MEDIAL2.max_cliques(4);
    }

    #[test]
    fn formula_and_back() {
        for x in u32::all_p4_free(5) {
            assert_eq!(u32::from_formula(&x.cograph_decomp(5)), x)
        }
    }

    #[test]
    fn switch() {
        assert!(linear_implication(&SW1MC, &SW2MC));
        assert!(!is_trivial(&SW1MC, &SW2MC, 3));
        assert!(is_switch(&*SWITCH1, &*SWITCH2, 3));
        assert!(!is_switch(&*MEDIAL1, &*MEDIAL2, 4));
    }

    #[test]
    fn medial() {
        assert!(linear_implication(&M1MC, &M2MC));
        assert!(!is_trivial(&M1MC, &M2MC, 4));
        assert!(is_medial_star(&*MEDIAL1, &*MEDIAL2, 4));
        assert!(!is_medial_star(&*SWITCH1, &*SWITCH2, 3));
    }

    #[test]
    fn rewrite() {
	assert!(is_rewrite(&*SWITCH1, &*SWITCH2, &*SWITCH1, &*SWITCH2, 3, 3));
	assert!(is_rewrite(&*MEDIAL1, &*MEDIAL2, &*MEDIAL1, &*MEDIAL2,4,4));
	assert!(!is_rewrite(&*SWITCH1, &*SWITCH2, &*MEDIAL1, &*MEDIAL2, 3, 4));
	assert!(!is_rewrite(&*MEDIAL1, &*MEDIAL2, &*SWITCH1, &*SWITCH2,4,3));
	assert!(is_rewrite(&*SWITCH1EX, &*SWITCH2EX, &*SWITCH1, &*SWITCH2, 4, 3));
    }

    #[test]
    fn build_id_u32() {
        for x in u32::all_p4_free(6) {
            assert_eq!(u32::build(|i, j| x.get(i, j), 6), x)
        }
    }

    #[test]
    fn build_id_vec() {
        for x in Vec::<bool>::all_p4_free(6) {
            assert_eq!(Vec::<bool>::build(|i, j| x.get(i, j), 6), x)
        }
    }

    #[test]
    fn rewrite_test_big() {
	assert!(is_rewrite(&14921438u32,&36833804u32,&14921438u32,&36833804u32,8,8))
    }
}
