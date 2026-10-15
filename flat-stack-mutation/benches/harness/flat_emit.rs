//! Compiles the shared language to the experiment's tape.
//!
//! Layout: every function is emitted as `FnStart .. body .. FnEnd`, callees
//! first, then `main` as straight-line tape. A call names its callee with a
//! backward `Ref` to that function's `FnEnd`; a self-recursive function is
//! entered through the `[self, self]` closure the VM's own tests use, so the
//! recursive call needs no forward reference.
//!
//! `if` compiles to two zero-argument thunks plus the condition, which is the
//! VM's `If`; a call in tail position is simply a call whose next tape slot is
//! an `FnEnd`, which is how the VM detects and collapses tail frames.

#![allow(dead_code)]

use std::collections::HashMap;

use super::flat::{BinOp, Op, Op::*, SizedOp, SizedOp::*};
use super::lang::{Expr, Func, Prim, Program, Takes, analyze, consuming, key};

#[derive(Debug, Clone, Copy)]
struct FnInfo {
    /// Tape index of the function's `FnEnd`.
    end: usize,
    rec: bool,
}

pub struct Emitter {
    code: Vec<Op>,
    fns: HashMap<&'static str, FnInfo>,
    /// When false, every operand is a borrow (`Var`) and the VM's in-place
    /// paths never fire: the copy-on-write cost model, measured.
    use_take: bool,
    current: Option<&'static str>,
}

/// `use_take`: emit `Take` for the list operand of a mutating primitive whose
/// binding is dead afterwards. This is the compiler's whole contribution to
/// in-place mutation; with it off, the same program runs copy-on-write.
pub fn compile(p: &Program, use_take: bool) -> Vec<Op> {
    let mut e = Emitter { code: vec![], fns: HashMap::new(), use_take, current: None };
    for f in &p.funcs {
        e.emit_fn(f);
    }
    let takes = analyze(&p.main);
    e.current = None;
    e.emit(&p.main, &[], &takes);
    e.code
}

impl Emitter {
    fn at(&self) -> usize {
        self.code.len()
    }

    fn push(&mut self, op: Op) {
        self.code.push(op);
    }

    /// A borrow of the tape slot at `target`, from the slot we are about to
    /// write (the VM resolves `Ref { offset }` against the ref's own index).
    fn push_ref(&mut self, target: usize) {
        let offset = self.at() - target;
        self.push(Ref { offset });
    }

    fn emit_fn(&mut self, f: &Func) {
        let takes = analyze(&f.body);
        let start = self.at();
        self.push(Sized(FnStart, 0));
        let mut params: Vec<&'static str> = vec![];
        if f.rec {
            params.push("self");
        }
        params.extend(f.params.iter().copied());
        // Registered before the body so a self-call resolves; the entry is
        // patched with the real `FnEnd` index below. A self-call never reads
        // it (it goes through `[self, self]`).
        self.fns.insert(f.name, FnInfo { end: usize::MAX, rec: f.rec });
        let outer = self.current.replace(f.name);
        self.emit(&f.body, &params, &takes);
        self.current = outer;
        let slots = self.at() - start - 1;
        self.code[start] = Sized(FnStart, slots);
        self.push(Sized(FnEnd { args: params.len() }, slots));
        let end = self.at() - 1;
        self.fns.insert(f.name, FnInfo { end, rec: f.rec });
    }

    /// A zero-argument thunk: it inherits the enclosing frame's bindings, so
    /// `Var` indices inside a branch are the same as outside.
    fn thunk(&mut self, body: &Expr, params: &[&'static str], takes: &Takes) {
        let start = self.at();
        self.push(Sized(FnStart, 0));
        self.emit(body, params, takes);
        let slots = self.at() - start - 1;
        self.code[start] = Sized(FnStart, slots);
        self.push(Sized(FnEnd { args: 0 }, slots));
    }

    fn emit(&mut self, e: &Expr, params: &[&'static str], takes: &Takes) {
        match e {
            Expr::Int(i) => self.push(Int(*i)),
            Expr::Var(x) => {
                let elem = index_of(params, x);
                self.push(Var { elem });
            }
            Expr::If(c, t, f) => {
                self.thunk(t, params, takes);
                self.thunk(f, params, takes);
                self.emit(c, params, takes);
                self.push(Sized(If, 0));
            }
            Expr::Call(name, args) => {
                let info = *self.fns.get(name).unwrap_or_else(|| panic!("unknown fn {name}"));
                if info.rec {
                    // `[self, self]`: element 0 is the code, element 1 is
                    // bound to the callee's `self` parameter.
                    if self.current == Some(*name) {
                        self.push(Var { elem: 0 });
                        self.push(Var { elem: 0 });
                    } else {
                        assert_ne!(info.end, usize::MAX, "{name} is not defined yet");
                        self.push_ref(info.end);
                        self.push_ref(info.end);
                    }
                    self.push(Sized(SizedOp::List { elems: 2 }, 0));
                } else {
                    self.push_ref(info.end);
                }
                for a in args {
                    // Every call argument is consumed by the callee.
                    self.operand(a, true, params, takes);
                }
                self.push(Sized(Call { args: args.len(), comptime: false }, 0));
            }
            Expr::Prim(p, args) => {
                for (i, a) in args.iter().enumerate() {
                    self.operand(a, consuming(*p, i), params, takes);
                }
                self.emit_prim(*p, args.len());
            }
        }
    }

    /// A variable in a consuming position at its last use is moved, not
    /// borrowed: that is the whole of the compiler's contribution to in-place
    /// mutation, and turning it off (`use_take = false`) leaves the same
    /// program running copy-on-write.
    fn operand(&mut self, a: &Expr, consumed: bool, params: &[&'static str], takes: &Takes) {
        match a {
            Expr::Var(x) if consumed && self.use_take && takes.get(&key(a)) == Some(&true) => {
                let elem = index_of(params, x);
                self.push(Take { elem });
            }
            _ => self.emit(a, params, takes),
        }
    }

    fn emit_prim(&mut self, p: Prim, argc: usize) {
        let bin = |b| Sized(Bin(b), 0);
        match p {
            Prim::Add => self.push(bin(BinOp::Add)),
            Prim::Sub => self.push(bin(BinOp::Sub)),
            Prim::Mul => self.push(bin(BinOp::Mul)),
            Prim::Div => self.push(bin(BinOp::Div)),
            Prim::Rem => self.push(bin(BinOp::Rem)),
            Prim::Eq => self.push(bin(BinOp::Eq)),
            Prim::Lt => self.push(bin(BinOp::Lt)),
            Prim::List => self.push(Sized(SizedOp::List { elems: argc }, 0)),
            Prim::Get => self.push(Sized(Get, 0)),
            Prim::Set => self.push(Sized(Set, 0)),
            Prim::Push => self.push(Sized(SizedOp::Push { elems: argc - 1 }, 0)),
            Prim::PopLast => self.push(Sized(Pop { elems: 1 }, 0)),
            Prim::Len => self.push(Sized(Len, 0)),
            Prim::IsNil => {
                self.push(Sized(Len, 0));
                self.push(Int(0));
                self.push(bin(BinOp::Eq));
            }
            Prim::Head => {
                self.push(Int(0));
                self.push(Sized(Get, 0));
            }
            Prim::Prepend | Prim::Tail => panic!("{p:?} has no flat counterpart"),
        }
    }
}

fn index_of(params: &[&'static str], x: &'static str) -> usize {
    params.iter().position(|p| *p == x).unwrap_or_else(|| panic!("unbound variable {x}"))
}
