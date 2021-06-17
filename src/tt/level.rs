use std::fmt::{Display, Formatter, Result as FmtResult};
use petgraph::{prelude::*, algo::FloatMeasure, dot::{Dot, Config as DotConfig}};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
struct EdgeWeight {
    infinite: i32,
    finite: i32,
}

impl EdgeWeight {
    pub fn finite(finite: i32) -> Self {
        EdgeWeight {
            infinite: 0,
            finite,
        }
    }
}

impl std::ops::Add for EdgeWeight {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        EdgeWeight {
            infinite: self.infinite + rhs.infinite,
            finite: self.finite + rhs.finite,
        }
    }
}

impl std::ops::Neg for EdgeWeight {
    type Output = Self;

    fn neg(self) -> Self::Output {
        EdgeWeight {
            infinite: -self.infinite,
            finite: -self.finite,
        }
    }
}

impl Display for EdgeWeight {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        if self.infinite == 0 {
            if self.finite == 0 {
                f.write_str("0")
            } else {
                Display::fmt(&self.finite, f)
            }
        } else if self.finite == 0 {
            write!(f, "{}ω", &self.infinite)
        } else {
            write!(f, "{}ω{:p}", &self.infinite, &self.finite)
        }
    }
}

impl FloatMeasure for EdgeWeight {
    fn zero() -> Self {
        EdgeWeight::default()
    }

    fn infinite() -> Self {
        EdgeWeight {
            infinite: 1,
            finite: 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Nothing;

impl Display for Nothing {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Ok(())
    }
}

type CtxGraph = DiGraph<Nothing, EdgeWeight, u32>;

pub type LevelVar = NodeIndex<u32>;

#[derive(Debug, Clone)]
pub struct LevelSystem(CtxGraph);

impl LevelSystem {
    pub fn new() -> Self {
        let mut graph = CtxGraph::new();
        let bottom = graph.add_node(Nothing);
        debug_assert_eq!(bottom, Self::bottom());
        LevelSystem(graph)
    }

    pub fn bottom() -> LevelVar {
        LevelVar::new(0)
    }

    pub fn fresh_level(&mut self, offset: i32) -> LevelVar {
        let node = self.0.add_node(Nothing);
        let bottom = Self::bottom();
        self.add_le_constraint(bottom, offset, node, 0);
        node
    }

    pub fn add_eq_constraint(&mut self, a: LevelVar, offset0: i32, b: LevelVar, offset1: i32) {
        self.add_le_constraint(a, offset0, b, offset1);
        self.add_le_constraint(b, offset1, a, offset0);
    }

    pub fn add_le_constraint(&mut self, a: LevelVar, offset0: i32, b: LevelVar, offset1: i32) {
        let offset = offset1 - offset0;
        if let Some(e1) = self.0.find_edge(a, b) {
            if self.0[e1] <= EdgeWeight::finite(offset) {
                self.0[e1] = EdgeWeight::finite(offset);
            }
        } else {
            self.0.add_edge(a, b, EdgeWeight::finite(offset));
        }
    }

    pub fn add_lt_constraint(&mut self, a: LevelVar, offset0: i32, b: LevelVar, offset1: i32) {
        self.add_le_constraint(a, offset0 + 1, b, offset1)
    }

    pub fn is_consistent(&self) -> bool {
        petgraph::algo::bellman_ford(&self.0, Self::bottom()).is_ok()
    }
}

impl Default for LevelSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for LevelSystem {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&Dot::with_config(&self.0, &[DotConfig::NodeIndexLabel]), f)
    }
}
