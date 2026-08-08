#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Slot {
    Int(i64),
    Var { elem: usize },
    Ref { offset: usize },
    Op(SlotOp, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SlotOp {
    FuncStart,
    FuncEnd,
    BlobStart,
    BlobEnd,
    Call { args: usize },
    Macro { args: usize },
    List { elems: usize },
    Set { index: Option<usize> },
    Get { index: Option<usize> },
    Push { elems: Option<usize> },
    Pop { elems: Option<usize> },
    If,
    Eq,
    Len,
    Rec,
}

use Slot::*;
use SlotOp::*;

impl Slot {
    fn size(&self) -> usize {
        match self {
            Op(FuncStart | FuncEnd | BlobStart | BlobEnd, slots) => slots + 2,
            Op(_, slots) => slots + 1,
            _ => 1,
        }
    }
}

#[derive(Debug)]
struct CallFrame {
    fp: usize,
    ret: usize,
    args: usize,
    slots: usize,
}

#[derive(Debug)]
pub struct Vm {
    ip: usize,
    end: usize,
    stack: Vec<Slot>,
    frames: Vec<CallFrame>,
}

impl Vm {
    pub fn load(code: Vec<Slot>) -> Self {
        Vm { ip: 0, end: code.len(), stack: code, frames: vec![] }
    }

    fn sp(&self) -> usize {
        self.stack.len() - 1
    }

    fn sum_size(&self, n: usize) -> usize {
        let mut sp = self.sp();
        for _ in 0..n {
            sp -= self.stack[sp].size();
        }
        self.sp() - sp
    }

    fn borrow(&self, src: usize, dst: usize) -> Result<Slot, String> {
        match self.stack[src] {
            Int(i) => Ok(Int(i)),
            Var { .. } => Err(format!("Var on the stack at {}", self.ip)),
            Ref { offset } => Ok(Ref { offset: offset + dst - src }),
            Op(_, _) => Ok(Ref { offset: dst - src }),
        }
    }

    fn push_borrows(&mut self, n: usize) -> Result<(), String> {
        let mut sp: usize = self.sp();
        let top = sp + n;
        self.stack.resize(self.stack.len() + n, Int(0));
        for i in 0..n {
            let slot = self.stack[sp];
            self.stack[top - i] = self.borrow(sp, top - i)?;
            sp -= slot.size();
        }
        Ok(())
    }

    fn pop_optional(&mut self, n: Option<usize>) -> Result<usize, String> {
        todo!()
    }

    fn pop(&mut self) -> Result<Slot, String> {
        self.stack.pop().ok_or_else(|| format!("Stack underflow at {}", self.ip))
    }

    fn resolve_slot(&self, sp: usize) -> Result<(usize, Slot), String> {
        match self.stack[sp] {
            Var { .. } => return Err(format!("Var on the stack at {}", self.ip)),
            Ref { offset } => Ok((sp - offset, self.stack[sp - offset])),
            slot => Ok((sp, slot)),
        }
    }

    fn resolve_var(&self, n: usize) -> Result<usize, String> {
        match self.frames.last() {
            None => return Err(format!("Expected call frame at {}", self.ip)),
            Some(CallFrame { args, .. }) if n >= *args => {
                return Err(format!("Var out of bounds at {}", self.ip));
            }
            Some(CallFrame { fp, ret: _, args, slots }) => Ok(fp + slots - args + n),
        }
    }

    fn eval_once(&mut self, comptime: bool) -> Result<(), String> {
        let Some(op) = self.stack.get(self.ip) else {
            return Err(format!("No op at instruction {}", self.ip));
        };
        match *op {
            Int(i) => {
                self.stack.push(Int(i));
                self.ip += 1;
            }
            Ref { offset } => {
                if offset == 0 || offset > self.ip {
                    return Err(format!("Invalid ref at {}", self.ip));
                }
                self.stack.push(self.borrow(self.ip - offset, self.stack.len())?);
                self.ip += 1;
            }
            Var { elem } => {
                self.stack.push(self.borrow(self.resolve_var(elem)?, self.stack.len())?);
                self.ip += 1;
            }
            Op(FuncStart, _) if comptime => todo!(),
            Op(FuncEnd, _) if comptime => todo!(),
            Op(FuncStart, slots) | Op(BlobStart, slots) => {
                self.stack.push(Ref { offset: self.sp() - self.ip - slots });
                self.ip += slots + 2;
            }
            Op(FuncEnd, _) => {
                let Some(CallFrame { fp: _, ret, args: _, slots: _ }) = self.frames.pop() else {
                    return Err(format!("No frame at {}", self.ip));
                };
                // TODO: run 4 pass compaction
                self.ip = ret;
            }
            Op(BlobEnd, _) => return Err(format!("Found blob end at {}", self.ip)),
            Op(Call { args }, _) if comptime => {
                self.stack.push(Op(Call { args }, self.sum_size(args)));
                self.ip += 1;
            }
            Op(Call { args }, _) => {
                let mut slots = self.sum_size(args);
                if slots > args {
                    self.push_borrows(args)?;
                    slots += args;
                }
                let (sp, f) = self.resolve_slot(self.sp() - slots)?;
                slots += self.stack[self.sp() - slots].size();
                self.frames.push(CallFrame {
                    fp: self.stack.len() - slots,
                    ret: self.ip + 1,
                    args,
                    slots,
                });
                match f {
                    Op(FuncEnd, slots) => self.ip = sp - slots,
                    slot => {
                        return Err(format!("Expected function at {}, found {slot:?}", self.ip));
                    }
                }
            }
            Op(Macro { args }, slots) => todo!(),
            Op(List { elems }, _) => {
                let mut slots = self.sum_size(elems);
                if slots > elems {
                    self.push_borrows(elems)?;
                    slots += elems;
                }
                self.stack.push(Op(List { elems }, slots));
                self.ip += 1;
            }
            Op(Set { index }, slots) => {
                // TODO: Make sure we make it impossible to create forward-refs
                todo!()
            }
            Op(Get { index }, slots) => {
                let index = self.pop_optional(index)?;
                match self.pop()? {
                    Op(List { elems }, _) if index >= elems => todo!(),
                    Op(List { elems }, _) => todo!(),
                    Ref { offset } => todo!(),
                    other => return Err(format!("Invalid list at {}: {other:?}", self.ip)),
                }
                // TODO: the actual logic
            }
            Op(Push { elems }, slots) => todo!(),
            Op(Pop { elems }, slots) => todo!(),
            Op(If, slots) => todo!(),
            Op(Eq, slots) => todo!(),
            Op(Len, slots) => todo!(),
            Op(Rec, slots) => todo!(),
        }
        Ok(())
    }

    pub fn run(mut self) -> Result<Vec<Slot>, String> {
        while self.ip != self.end {
            self.eval_once(false)?;
        }
        Ok(self.stack)
    }
}
