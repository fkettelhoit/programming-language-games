use Op::*;
use SizedOp::*;
use flat_stack_mutation::{BinOp, Op, SizedOp, Vm};

fn run(program: Vec<Op>, comptime: bool) -> Vec<Op> {
    let mut vm = Vm::load(program);
    if let Err(e) = vm.run(comptime) {
        panic!("VM error: {e}\n{vm:#?}");
    }
    vm.stack.into_iter().map(|slot| slot.op).collect()
}
