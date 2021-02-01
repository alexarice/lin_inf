use crate::formula::*;
use crate::mclique::MClique;
use crate::permutation::Permutation;
use crate::Node;
use itertools::{Either, Itertools};
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

pub trait LinGraph: Sized + Eq {
    fn get(&self, x: Node, y: Node) -> bool;
    fn build<T>(f: T, number_vars: usize) -> Self
    where
        T: Fn(Node, Node) -> bool;
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
    fn all_p4_free(number_vars: usize) -> Vec<Self>;
    fn neighbours(&self, number_vars: usize, x: Node) -> HashSet<Node> {
        (0..number_vars).filter(|&m| self.get(x, m)).collect()
    }
    fn apply_perm(&self, p: &Permutation) -> Self {
        let pinv = p.invert();
        Self::build(|x, y| self.get(pinv.ap(x), pinv.ap(y)), p.len())
    }
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
    fn is_and_partition(&self, a: &Vec<Node>, b: &Vec<Node>) -> bool {
        a.iter().all(|&x| b.iter().all(|&y| self.get(x, y)))
    }

    fn is_or_partition(&self, a: &Vec<Node>, b: &Vec<Node>) -> bool {
        a.iter().all(|&x| b.iter().all(|&y| !self.get(x, y)))
    }

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

    fn from_formula(f: &Formula) -> Self {
        Self::build(|x, y| f.least_common_connective(x, y) == Some(And), f.len())
    }
}

fn calc_bit(x: Node, y: Node) -> usize {
    (1..y).sum::<usize>() + x
}

macro_rules! impl_lg {
    ( $x : ty ) => {
        impl LinGraph for $x {
            fn get(&self, x: Node, y: Node) -> bool {
                if x == y {
                    false
                } else if x > y {
                    self.get(y, x)
                } else {
                    *self & 1 << calc_bit(x, y) != 0
                }
            }
            fn all_p4_free(n: usize) -> Vec<$x> {
                let reduced_p4 = |x: Self| {
                    (0..n - 1).permutations(3).all(|v| {
                        let (a, b, c) = v.into_iter().collect_tuple().unwrap();
                        !(x.get(n - 1, a)
                            && !(x.get(n - 1, b))
                            && !(x.get(n - 1, c))
                            && x.get(a, b)
                            && !(x.get(a, c))
                            && x.get(b, c))
                            && !(x.get(a, n - 1)
                                && !(x.get(a, b))
                                && !(x.get(a, c))
                                && x.get(n - 1, b)
                                && !(x.get(n - 1, c))
                                && x.get(b, c))
                    })
                };
                match n {
                    0 => {
                        vec![0]
                    }
                    _ => {
                        let m = n - 1;
                        let p4_free = Self::all_p4_free(m);
                        let new_graphs = p4_free
                            .into_iter()
                            .cartesian_product(0..((2 as $x).pow(m as u32)))
                            .par_bridge()
                            .map(move |(x, y)| x + (y << (0..(m as $x)).sum::<$x>()));
                        new_graphs.filter(|&x| reduced_p4(x)).collect()
                    }
                }
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
    fn all_p4_free(n: usize) -> Vec<Self> {
        let reduced_p4 = |x: &Self| {
            (0..n - 1).permutations(3).all(|v| {
                let (a, b, c) = v.into_iter().collect_tuple().unwrap();
                !(x.get(n - 1, a)
                    && !(x.get(n - 1, b))
                    && !(x.get(n - 1, c))
                    && x.get(a, b)
                    && !(x.get(a, c))
                    && x.get(b, c))
                    && !(x.get(a, n - 1)
                        && !(x.get(a, b))
                        && !(x.get(a, c))
                        && x.get(n - 1, b)
                        && !(x.get(n - 1, c))
                        && x.get(b, c))
            })
        };
        match n {
            0 => {
                vec![vec![]]
            }
            _ => {
                let m = n - 1;
                let p4_free = Self::all_p4_free(m);
                let new_graphs = p4_free
                    .into_iter()
                    .cartesian_product(
                        [false, true]
                            .iter()
                            .cloned()
                            .combinations_with_replacement(m),
                    )
                    .par_bridge()
                    .map(move |(mut x, mut y)| {
                        x.append(&mut y);
                        x
                    });
                new_graphs.filter(|x| reduced_p4(x)).collect()
            }
        }
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

pub fn is_switch<T: LinGraph>(lg1: &T, lg2: &T, number_vars: usize) -> bool {
    is_switch_help(lg1, lg2, &(0..number_vars).collect())
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
}
