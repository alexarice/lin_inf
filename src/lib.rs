#[cfg(test)]
#[macro_use]
extern crate lazy_static;
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub type Node = usize;

pub mod formula;
pub mod lin_graph;
pub mod mclique;
pub mod permutation;
