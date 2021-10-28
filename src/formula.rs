use crate::Node;
use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Connective {
    And,
    Or,
}

pub use Connective::*;

impl Display for Connective {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            // And => write!(f, "∧"),
            // Or => write!(f, "∨"),
	    And => write!(f, "\\land"),
            Or => write!(f, "\\lor"),
        }
    }
}

#[derive(Debug)]
pub enum Formula {
    Var(Node),
    Con(Connective, Box<Formula>, Box<Formula>),
}

pub use Formula::*;

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
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
    pub fn and(self, f: Formula) -> Formula {
        Con(And, Box::new(self), Box::new(f))
    }
    pub fn or(self, f: Formula) -> Formula {
        Con(Or, Box::new(self), Box::new(f))
    }
    fn find(&self, n: Node) -> Option<Vec<Direction>> {
        match self {
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

    pub fn len(&self) -> usize {
        match self {
            Var(_) => 1,
            Con(_, x, y) => x.len() + y.len(),
        }
    }

    pub fn least_common_connective(&self, n: Node, m: Node) -> Option<Connective> {
        fn helper(
            f: &Formula,
            vn: &mut Vec<Direction>,
            vm: &mut Vec<Direction>,
        ) -> Option<Connective> {
            match f {
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
}
