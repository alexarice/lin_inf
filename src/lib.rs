//! A library for working with linear inferences represented as graphs

#[cfg(test)]
#[macro_use]
extern crate lazy_static;
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

/// Type for representing nodes in a graph
pub type Node = usize;

pub mod formula;
pub mod lin_graph;
pub mod mclique;
pub mod permutation;
