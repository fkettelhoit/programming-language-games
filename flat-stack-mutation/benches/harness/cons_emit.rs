//! Compiles the shared language to the cons VM's bytecode.
//!
//! Conventional: functions are entered by direct call, `if` is a conditional
//! jump (no branch thunks), and a call in tail position becomes `TailCall`,
//! so the cons VM gets tail-call elimination too.
//!
//! The one non-obvious part is ownership. A variable read in a position that
//! wants to own the value is retained; a variable read by a primitive that
//! only inspects it is borrowed (no reference-count traffic); and the list
//! operand of an updating primitive at its last use is *moved* — the same
//! last-use analysis that drives the flat backend's `Take`. Without the move
//! the binding would hold a second reference and reuse could never fire.

#![allow(dead_code)]

use std::collections::HashMap;

use super::cons::{Arg0, Ins};
use super::lang::{Expr, Func, Prim, Program, Takes, analyze, consuming, key};

pub struct Code {
    pub ins: Vec<Ins>,
    pub entry: usize,
}

pub fn compile(p: &Program) -> Code {
    let mut e = Emitter { ins: vec![], fns: HashMap::new() };
    for f in &p.funcs {
        e.emit_fn(f);
    }
    let entry = e.ins.len();
    let takes = analyze(&p.main);
    e.emit(&p.main, &[], &takes, false);
    e.ins.push(Ins::Halt);
    Code { ins: e.ins, entry }
}

struct Emitter {
    ins: Vec<Ins>,
    fns: HashMap<&'static str, usize>,
}

fn read_only(p: Prim) -> bool {
    matches!(p, Prim::Get | Prim::Head | Prim::Tail | Prim::Len | Prim::IsNil)
}

impl Emitter {
    fn emit_fn(&mut self, f: &Func) {
        let takes = analyze(&f.body);
        let entry = self.ins.len();
        self.fns.insert(f.name, entry);
        let env: Vec<&'static str> = f.params.clone();
        self.emit(&f.body, &env, &takes, true);
        self.ins.push(Ins::Ret);
    }

    fn emit(&mut self, e: &Expr, env: &[&'static str], takes: &Takes, tail: bool) {
        match e {
            Expr::Int(i) => self.ins.push(Ins::Const(*i)),
            Expr::Var(x) => self.ins.push(Ins::Local(index_of(env, x))),
            Expr::If(c, t, f) => {
                self.emit(c, env, takes, false);
                let j1 = self.hole();
                self.emit(t, env, takes, tail);
                let j2 = self.hole();
                self.ins[j1] = Ins::JumpIfZero(self.ins.len());
                self.emit(f, env, takes, tail);
                self.ins[j2] = Ins::Jump(self.ins.len());
            }
            Expr::Call(name, args) => {
                let mut moves = vec![];
                for a in args {
                    self.operand(a, true, env, takes, &mut moves);
                }
                self.clears(&moves);
                let entry = *self.fns.get(name).unwrap_or_else(|| panic!("unknown fn {name}"));
                let args = args.len();
                self.ins.push(if tail {
                    Ins::TailCall { entry, args }
                } else {
                    Ins::Call { entry, args }
                });
            }
            Expr::Prim(p, args) => {
                let mut arg0 = Arg0::Owned;
                let mut moves = vec![];
                for (i, a) in args.iter().enumerate() {
                    match a {
                        // A primitive that only inspects its operand borrows
                        // it: no reference-count traffic at all.
                        Expr::Var(x) if i == 0 && read_only(*p) => {
                            arg0 = Arg0::Borrowed;
                            self.ins.push(Ins::LocalRaw(index_of(env, x)));
                        }
                        _ => self.operand(a, consuming(*p, i), env, takes, &mut moves),
                    }
                }
                self.clears(&moves);
                match p {
                    Prim::List => self.ins.push(Ins::MakeList(args.len())),
                    _ => self.ins.push(Ins::Prim(*p, arg0)),
                }
            }
        }
    }

    /// A variable in a consuming position at its last use hands over the
    /// binding's reference instead of retaining a second one; the slot is
    /// emptied by a `Clear` once every operand has been evaluated.
    fn operand(
        &mut self,
        a: &Expr,
        consumed: bool,
        env: &[&'static str],
        takes: &Takes,
        moves: &mut Vec<usize>,
    ) {
        match a {
            Expr::Var(x) if consumed && takes.get(&key(a)) == Some(&true) => {
                let slot = index_of(env, x);
                self.ins.push(Ins::LocalRaw(slot));
                moves.push(slot);
            }
            _ => self.emit(a, env, takes, false),
        }
    }

    fn clears(&mut self, moves: &[usize]) {
        for slot in moves {
            self.ins.push(Ins::Clear(*slot));
        }
    }

    fn hole(&mut self) -> usize {
        self.ins.push(Ins::Halt);
        self.ins.len() - 1
    }
}

fn index_of(env: &[&'static str], x: &'static str) -> usize {
    env.iter().position(|p| *p == x).unwrap_or_else(|| panic!("unbound variable {x}"))
}
