//! A tiny first-order functional language, shared by both backends.
//!
//! Every benchmark program is written once here and compiled twice: to the
//! flat VM's tape and to the cons VM's bytecode. That keeps the comparison
//! about the two memory models rather than about who hand-optimised harder.
//!
//! The language has no `let`: bindings are function parameters, which is all
//! the flat VM offers (`Var { elem }` indexes the current frame's arguments).
//! Recursion is self-recursion only; on the flat side it goes through the
//! self-capturing closure `[self, self]` that the VM's tests use.
//!
//! `Prepend`/`Tail` are cons-only primitives (a flat list has no O(1) front),
//! so programs written in the cons idiom simply do not compile for the flat
//! VM. That asymmetry is a finding, not a rigged benchmark: each task below
//! is expressed in whichever idiom each model is meant to be programmed in.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Prim {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Lt,
    /// `list(e0, .., en)` — build a list from n operands.
    List,
    /// `get(l, i)` — element at index i.
    Get,
    /// `set(l, v, i)` — l with index i replaced by v.
    Set,
    /// `push(l, e)` — l with e appended at the end.
    Push,
    /// `pop_last(l)` — l without its last element.
    PopLast,
    Len,
    IsNil,
    /// `prepend(e, l)` — cons-only: e in front of l, O(1).
    Prepend,
    /// `head(l)` — first element.
    Head,
    /// `tail(l)` — cons-only: everything but the first element, O(1).
    Tail,
}

impl Prim {
    /// Primitives whose first operand is the list being updated: the only
    /// place where a `Take` (move) can turn a copy into an in-place write.
    pub fn mutates(self) -> bool {
        matches!(self, Prim::Set | Prim::Push | Prim::PopLast)
    }

    pub fn flat_supported(self) -> bool {
        !matches!(self, Prim::Prepend | Prim::Tail)
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i64),
    Var(&'static str),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(&'static str, Vec<Expr>),
    Prim(Prim, Vec<Expr>),
}

#[derive(Debug, Clone)]
pub struct Func {
    pub name: &'static str,
    pub params: Vec<&'static str>,
    pub body: Expr,
    /// Self-recursive: gets an implicit leading `self` parameter on the flat
    /// side (the closure protocol) and a self-entry on the cons side.
    pub rec: bool,
}

#[derive(Debug, Clone)]
pub struct Program {
    /// Callees first: a call may only name a function defined before it (or
    /// itself, when `rec`).
    pub funcs: Vec<Func>,
    pub main: Expr,
}

impl Program {
    pub fn uses_prim(&self, p: Prim) -> bool {
        fn walk(e: &Expr, p: Prim) -> bool {
            match e {
                Expr::Int(_) | Expr::Var(_) => false,
                Expr::If(c, t, f) => walk(c, p) || walk(t, p) || walk(f, p),
                Expr::Call(_, args) => args.iter().any(|a| walk(a, p)),
                Expr::Prim(q, args) => *q == p || args.iter().any(|a| walk(a, p)),
            }
        }
        walk(&self.main, p) || self.funcs.iter().any(|f| walk(&f.body, p))
    }

    pub fn runs_on_flat(&self) -> bool {
        !self.uses_prim(Prim::Prepend) && !self.uses_prim(Prim::Tail)
    }
}

// --- constructors ----------------------------------------------------------

pub fn int(i: i64) -> Expr {
    Expr::Int(i)
}
pub fn var(n: &'static str) -> Expr {
    Expr::Var(n)
}
pub fn iff(c: Expr, t: Expr, f: Expr) -> Expr {
    Expr::If(Box::new(c), Box::new(t), Box::new(f))
}
pub fn call(f: &'static str, args: Vec<Expr>) -> Expr {
    Expr::Call(f, args)
}
pub fn add(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Add, vec![a, b])
}
pub fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Sub, vec![a, b])
}
pub fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Mul, vec![a, b])
}
pub fn div(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Div, vec![a, b])
}
pub fn rem(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Rem, vec![a, b])
}
pub fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Eq, vec![a, b])
}
pub fn lt(a: Expr, b: Expr) -> Expr {
    Expr::Prim(Prim::Lt, vec![a, b])
}
pub fn list(items: Vec<Expr>) -> Expr {
    Expr::Prim(Prim::List, items)
}
pub fn nil() -> Expr {
    Expr::Prim(Prim::List, vec![])
}
pub fn get(l: Expr, i: Expr) -> Expr {
    Expr::Prim(Prim::Get, vec![l, i])
}
pub fn set(l: Expr, v: Expr, i: Expr) -> Expr {
    Expr::Prim(Prim::Set, vec![l, v, i])
}
pub fn push(l: Expr, e: Expr) -> Expr {
    Expr::Prim(Prim::Push, vec![l, e])
}
pub fn pop_last(l: Expr) -> Expr {
    Expr::Prim(Prim::PopLast, vec![l])
}
pub fn len(l: Expr) -> Expr {
    Expr::Prim(Prim::Len, vec![l])
}
pub fn is_nil(l: Expr) -> Expr {
    Expr::Prim(Prim::IsNil, vec![l])
}
pub fn prepend(e: Expr, l: Expr) -> Expr {
    Expr::Prim(Prim::Prepend, vec![e, l])
}
pub fn head(l: Expr) -> Expr {
    Expr::Prim(Prim::Head, vec![l])
}
pub fn tail(l: Expr) -> Expr {
    Expr::Prim(Prim::Tail, vec![l])
}

pub fn func(name: &'static str, params: Vec<&'static str>, body: Expr) -> Func {
    Func { name, params, body, rec: false }
}
pub fn rec(name: &'static str, params: Vec<&'static str>, body: Expr) -> Func {
    Func { name, params, body, rec: true }
}

// --- last-use analysis -----------------------------------------------------

/// Positions where the value is stored or handed on, so the operand must own
/// it: constructor elements, call arguments, and the list (and new element)
/// of an updating primitive. Everything else — arithmetic, `get`, `len` — only
/// inspects its operand and can borrow it.
pub fn consuming(p: Prim, i: usize) -> bool {
    match p {
        Prim::List | Prim::Prepend => true,
        Prim::Set | Prim::Push => i < 2,
        Prim::PopLast => i == 0,
        _ => false,
    }
}

/// Decisions keyed by the address of the operand node they belong to.
pub type Takes = HashMap<usize, bool>;

pub fn key(e: &Expr) -> usize {
    e as *const Expr as usize
}

/// For every variable in a consuming position, decide whether it can be
/// moved rather than borrowed.
///
/// Both backends turn a `true` here into a move: the flat VM's `Take`, the
/// cons VM's `LocalRaw` + `Clear`. Both are two-phase — the binding stays
/// readable until the consuming op runs — so operands evaluated after the
/// reservation may still read the variable. `set(take l, get(l, i) + 1, i)`
/// is exactly the read-modify-write this exists for.
///
/// Two conditions. The variable must be dead after the operation that
/// consumes it, which is ordinary backward liveness. And it must not already
/// have been moved by an operation that runs *later*: `f(l, g(set(l, ..)))`
/// hands `l` to `f`, so the inner `set` may not move it out from under the
/// pending argument — it has to copy. Because an operation consumes its
/// operands after its whole subtree has run, the outer decision is taken
/// first in this backward walk, and inner ones see it in `moved`.
pub fn analyze(body: &Expr) -> Takes {
    let mut live = HashSet::new();
    let mut moved = HashSet::new();
    let mut out = Takes::new();
    walk(body, &mut live, &mut moved, &mut out);
    out
}

type Vars = HashSet<&'static str>;

fn walk(e: &Expr, live: &mut Vars, moved: &mut Vars, out: &mut Takes) {
    match e {
        Expr::Int(_) => {}
        Expr::Var(x) => {
            live.insert(x);
        }
        Expr::If(c, t, f) => {
            // Only one branch runs, so each branch sees the same live-out set
            // and a last use inside a branch really is a last use.
            let (mut live_t, mut moved_t) = (live.clone(), moved.clone());
            walk(t, &mut live_t, &mut moved_t, out);
            let (mut live_f, mut moved_f) = (live.clone(), moved.clone());
            walk(f, &mut live_f, &mut moved_f, out);
            *live = live_t.union(&live_f).copied().collect();
            *moved = moved_t.union(&moved_f).copied().collect();
            walk(c, live, moved, out);
        }
        Expr::Call(_, args) | Expr::Prim(_, args) => {
            let owned: Vec<bool> = match e {
                Expr::Call(..) => vec![true; args.len()],
                Expr::Prim(p, _) => (0..args.len()).map(|i| consuming(*p, i)).collect(),
                _ => unreachable!(),
            };
            // `live` is still the live-out set of this operation, which is
            // where its own operands are consumed.
            for (i, a) in args.iter().enumerate() {
                if owned[i]
                    && let Expr::Var(x) = a
                {
                    let m = !live.contains(x) && !moved.contains(x);
                    out.insert(key(a), m);
                    if m {
                        moved.insert(x);
                    }
                }
            }
            for a in args.iter().rev() {
                walk(a, live, moved, out);
            }
        }
    }
}
