//! Data structures and tools for working with formulae

use crate::Node;
use std::fmt::{Display, Formatter, Result};

/// Data type for connectives
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Connective {
    /// Conjunction
    And,
    /// Disjunction
    Or,
}

pub use Connective::*;

/// For printing a connective in latex format
impl Display for Connective {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
	    And => write!(f, "\\land"),
            Or => write!(f, "\\lor"),
        }
    }
}

/// Recursive data type for representing formulae
#[derive(Debug,Clone)]
pub enum Formula {
    Const(bool),
    Var(Node),
    Con(Connective, Box<Formula>, Box<Formula>),
}

pub use Formula::*;

/// For printing a formula in latex format
impl Display for Formula {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
	    Const(true) => {
		write!(f,"\\top")
	    }
	    Const(false) => {
		write!(f,"\\bot")
	    }
            Var(s) => {
                write!(f, "{}", s)
            }
            Con(c, x, y) => {
                write!(f, "({} {} {})", *x, c, *y)
            }
        }
    }
}

#[derive(PartialEq)]
enum Direction {
    L,
    R,
}
use Direction::*;

impl Formula {
    /// Create the conjunction of two formulae
    pub fn and(self, f: Formula) -> Formula {
        Con(And, Box::new(self), Box::new(f))
    }

    /// Create the disjunction of two formulae
    pub fn or(self, f: Formula) -> Formula {
        Con(Or, Box::new(self), Box::new(f))
    }

    fn find(&self, n: Node) -> Option<Vec<Direction>> {
        match self {
	    Const(_) => None,
            Var(m) => {
                if *m == n {
                    Some(vec![])
                } else {
                    None
                }
            }
            Con(_, x, y) => x
                .find(n)
                .map(|mut v| {
                    v.push(L);
                    v
                })
                .or_else(|| {
                    y.find(n).map(|mut v| {
                        v.push(R);
                        v
                    })
                }),
        }
    }

    /// Simplify a formula as far as possible by applying unit rules.
    pub fn simplify(self) -> Formula {
	match self {
	    Con(c,x,y) => {
		match (c,x.simplify(),y.simplify()) {
		    (And, Const(true), ys) => ys,
		    (And, Const(false), _) => Const(false),
		    (And, xs, Const(true)) => xs,
		    (And, _, Const(false)) => Const(false),
		    (Or, Const(true), _) => Const(true),
		    (Or, Const(false), ys) => ys,
		    (Or, _, Const(true) ) => Const(true),
		    (Or, xs, Const(false)) => xs,
		    (c, xs, ys) => Con(c,Box::new(xs),Box::new(ys))
		}
	    }
	    x => x
	}
    }

    /// Obtain the number of variables in a formula.
    pub fn len(&self) -> usize {
        match self {
	    Const(_) => 0,
            Var(_) => 1,
            Con(_, x, y) => x.len() + y.len(),
        }
    }

    /// Replace variables in a formula with specified subformulae.
    pub fn map_formula<T>(&self, f: &T) -> Formula
    where T: Fn (Node) -> Formula {
	match self {
	    Const(b) => Const(*b),
	    Var(x) => f(*x),
	    Con(c, x, y) => Con(*c, Box::new(x.map_formula(f)), Box::new(y.map_formula(f)))
	}
    }

    /// Returns the least common connective of two variables, if it exists
    pub fn least_common_connective(&self, n: Node, m: Node) -> Option<Connective> {
        fn helper(
            f: &Formula,
            vn: &mut Vec<Direction>,
            vm: &mut Vec<Direction>,
        ) -> Option<Connective> {
            match f {
		Const(_) => None,
                Var(_) => None,
                Con(c, x, y) => vn.pop().and_then(|n| {
                    vm.pop().and_then(|m| {
                        if n == m {
                            if n == L {
                                helper(x, vn, vm)
                            } else {
                                helper(y, vn, vm)
                            }
                        } else {
                            Some(*c)
                        }
                    })
                }),
            }
        }
        self.find(n)
            .as_mut()
            .and_then(|vn| self.find(m).as_mut().and_then(|vm| helper(self, vn, vm)))
    }

    /// Check if a formula contains any constants.
    pub fn unit_free(&self) -> bool {
	match self {
	    Const(_) => false,
	    Var(_) => true,
	    Con(_,x,y) => x.unit_free() && y.unit_free()
	}
    }
}
