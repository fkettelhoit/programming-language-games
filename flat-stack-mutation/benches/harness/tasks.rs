//! The benchmark programs.
//!
//! Each task is a job to do, not a fixed instruction sequence: it is written
//! once per *idiom* and every backend that can run that idiom does.
//!
//! - **index**: lists are indexed and updated at a position, and grown and
//!   shrunk at the end. This is the flat VM's whole vocabulary (it has no
//!   O(1) front), and the cons VM can run it too — usually badly, which is
//!   the point.
//! - **walk**: lists are consumed from the front with `head`/`tail` and built
//!   with `prepend`. This is how a cons-cell language is actually programmed,
//!   and the flat VM cannot run it at all: it has no primitive for either.
//!
//! Every variant of a task returns the same integer, which the runner checks,
//! so "different programs" cannot quietly become "different work".
//!
//! Checksums are order-sensitive (`acc * 31 + x mod 1000003`) except where a
//! task legitimately visits elements in a different order on each side, where
//! a plain sum is used instead.

#![allow(dead_code)]

use super::lang::*;
use super::run::Backend;

const M: i64 = 1_000_003;
/// An odd stride, so `i * STRIDE mod n` is a permutation for power-of-two n.
const STRIDE: i64 = 7919;

pub struct Variant {
    pub idiom: &'static str,
    pub build: fn(usize) -> Program,
}

pub struct Task {
    pub name: &'static str,
    pub about: &'static str,
    /// What `n` means in the per-element column.
    pub unit: &'static str,
    pub elems: fn(usize) -> usize,
    pub sizes: &'static [usize],
    pub variants: Vec<Variant>,
}

pub fn backends_for(p: &Program) -> Vec<Backend> {
    let mut v = vec![];
    if p.runs_on_flat() {
        v.push(Backend::Flat);
        // Without a mutating primitive the shared run is the same program.
        if p.uses_prim(Prim::Set) || p.uses_prim(Prim::Push) || p.uses_prim(Prim::PopLast) {
            v.push(Backend::FlatShared);
        }
    }
    v.push(Backend::ConsPersistent);
    v.push(Backend::ConsReuse);
    v
}

fn ident(n: usize) -> usize {
    n
}

// --- shared helpers --------------------------------------------------------

/// `acc * 31 + x mod M`
fn chk(acc: Expr, x: Expr) -> Expr {
    rem(add(mul(acc, int(31)), x), int(M))
}

/// `chk_i(l, n, i, acc)` — checksum by index.
fn chk_i() -> Func {
    rec(
        "chk_i",
        vec!["l", "n", "i", "acc"],
        iff(
            eq(var("i"), var("n")),
            var("acc"),
            call(
                "chk_i",
                vec![
                    var("l"),
                    var("n"),
                    add(var("i"), int(1)),
                    chk(var("acc"), get(var("l"), var("i"))),
                ],
            ),
        ),
    )
}

/// `chk_w(l, acc)` — checksum by walking the spine.
fn chk_w() -> Func {
    rec(
        "chk_w",
        vec!["l", "acc"],
        iff(
            is_nil(var("l")),
            var("acc"),
            call("chk_w", vec![tail(var("l")), chk(var("acc"), head(var("l")))]),
        ),
    )
}

fn pair_sum() -> Func {
    func("pair_sum", vec!["p"], add(get(var("p"), int(0)), get(var("p"), int(1))))
}

/// Checksum of a list of pairs, by index.
fn chkp_i() -> Func {
    rec(
        "chkp_i",
        vec!["l", "n", "i", "acc"],
        iff(
            eq(var("i"), var("n")),
            var("acc"),
            call(
                "chkp_i",
                vec![
                    var("l"),
                    var("n"),
                    add(var("i"), int(1)),
                    chk(var("acc"), call("pair_sum", vec![get(var("l"), var("i"))])),
                ],
            ),
        ),
    )
}

/// Checksum of a list of pairs, by walking the spine.
fn chkp_w() -> Func {
    rec(
        "chkp_w",
        vec!["l", "acc"],
        iff(
            is_nil(var("l")),
            var("acc"),
            call(
                "chkp_w",
                vec![tail(var("l")), chk(var("acc"), call("pair_sum", vec![head(var("l"))]))],
            ),
        ),
    )
}

/// `build_i(l, n, i)` — append 0..n at the end, one at a time.
fn build_i() -> Func {
    rec(
        "build_i",
        vec!["l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call("build_i", vec![push(var("l"), var("i")), var("n"), add(var("i"), int(1))]),
        ),
    )
}

/// `build_w(l, i)` — prepend i..0 at the front, one at a time.
fn build_w() -> Func {
    rec(
        "build_w",
        vec!["l", "i"],
        iff(
            lt(var("i"), int(0)),
            var("l"),
            call("build_w", vec![prepend(var("i"), var("l")), sub(var("i"), int(1))]),
        ),
    )
}

fn built_i(n: usize) -> Expr {
    call("build_i", vec![nil(), int(n as i64), int(0)])
}

fn built_w(n: usize) -> Expr {
    call("build_w", vec![nil(), int(n as i64 - 1)])
}

fn sum_i(l: Expr, n: usize) -> Expr {
    call("chk_i", vec![l, int(n as i64), int(0), int(0)])
}

fn sum_w(l: Expr) -> Expr {
    call("chk_w", vec![l, int(0)])
}

// --- cons cells built out of flat primitives -------------------------------
//
// A cons cell is just a two-element list `[head, tail]`, so the tape can host
// one with no new primitives: `prepend` is `list(x, l)`, `head`/`tail` are
// `get(c, 0)`/`get(c, 1)`, and nil is the empty list. The tail is always
// older than the cell pointing at it, so the tape's backwards-only reference
// rule is satisfied by construction — which is exactly what a flat list
// cannot promise about its own elements.
//
// On the cons VM the same program costs two real cells per logical cell, so
// this idiom is a handicap there; it is included on both so the emulation's
// price is visible on each.

fn pcons(x: Expr, l: Expr) -> Expr {
    list(vec![x, l])
}
fn pcar(c: Expr) -> Expr {
    get(c, int(0))
}
fn pcdr(c: Expr) -> Expr {
    get(c, int(1))
}
fn pnil(c: Expr) -> Expr {
    eq(len(c), int(0))
}

/// `chk_p(l, acc)` — checksum by walking a chain of pairs.
fn chk_p() -> Func {
    rec(
        "chk_p",
        vec!["l", "acc"],
        iff(
            pnil(var("l")),
            var("acc"),
            call("chk_p", vec![pcdr(var("l")), chk(var("acc"), pcar(var("l")))]),
        ),
    )
}

/// `build_p(l, i)` — cons i..0 onto the front.
fn build_p() -> Func {
    rec(
        "build_p",
        vec!["l", "i"],
        iff(
            lt(var("i"), int(0)),
            var("l"),
            call("build_p", vec![pcons(var("i"), var("l")), sub(var("i"), int(1))]),
        ),
    )
}

fn built_p(n: usize) -> Expr {
    call("build_p", vec![nil(), int(n as i64 - 1)])
}

fn sum_p(l: Expr) -> Expr {
    call("chk_p", vec![l, int(0)])
}

fn build_pairs(n: usize) -> Program {
    Program { funcs: vec![chk_p(), build_p()], main: sum_p(built_p(n)) }
}

/// The textbook non-tail-recursive map, on tape-hosted cons cells.
fn map_pairs(n: usize) -> Program {
    let map_p = rec(
        "map_p",
        vec!["l"],
        iff(
            pnil(var("l")),
            var("l"),
            pcons(add(pcar(var("l")), int(1)), call("map_p", vec![pcdr(var("l"))])),
        ),
    );
    Program { funcs: vec![chk_p(), build_p(), map_p], main: sum_p(call("map_p", vec![built_p(n)])) }
}

/// n versions of one shared chain, each with a different head: the structural
/// sharing case, expressed with tape primitives.
fn fork_head_pairs(n: usize) -> Program {
    let fork_p = rec(
        "fork_p",
        vec!["base", "m", "j", "acc"],
        iff(
            eq(var("j"), var("m")),
            var("acc"),
            call(
                "fork_p",
                vec![
                    var("base"),
                    var("m"),
                    add(var("j"), int(1)),
                    chk(var("acc"), pcar(pcons(var("j"), pcdr(var("base"))))),
                ],
            ),
        ),
    );
    Program {
        funcs: vec![build_p(), fork_p],
        main: call("fork_p", vec![built_p(n), int(n as i64), int(0), int(0)]),
    }
}

// --- 1. build --------------------------------------------------------------

fn build_index(n: usize) -> Program {
    Program { funcs: vec![chk_i(), build_i()], main: sum_i(built_i(n), n) }
}

fn build_walk(n: usize) -> Program {
    Program { funcs: vec![chk_w(), build_w()], main: sum_w(built_w(n)) }
}

// --- 2. random access ------------------------------------------------------

/// `rnd(l, n, i, acc)` — n reads at i * STRIDE mod n.
fn rnd() -> Func {
    rec(
        "rnd",
        vec!["l", "n", "i", "acc"],
        iff(
            eq(var("i"), var("n")),
            var("acc"),
            call(
                "rnd",
                vec![
                    var("l"),
                    var("n"),
                    add(var("i"), int(1)),
                    chk(var("acc"), get(var("l"), rem(mul(var("i"), int(STRIDE)), var("n")))),
                ],
            ),
        ),
    )
}

fn random_index(n: usize) -> Program {
    Program {
        funcs: vec![build_i(), rnd()],
        main: call("rnd", vec![built_i(n), int(n as i64), int(0), int(0)]),
    }
}

fn random_walk(n: usize) -> Program {
    Program {
        funcs: vec![build_w(), rnd()],
        main: call("rnd", vec![built_w(n), int(n as i64), int(0), int(0)]),
    }
}

// --- 3. map ----------------------------------------------------------------

/// `map_i(l, n, i)` — add 1 to every element, updating in place.
fn map_i() -> Func {
    rec(
        "map_i",
        vec!["l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call(
                "map_i",
                vec![
                    set(var("l"), add(get(var("l"), var("i")), int(1)), var("i")),
                    var("n"),
                    add(var("i"), int(1)),
                ],
            ),
        ),
    )
}

/// `map_w(l)` — the textbook non-tail-recursive rebuild.
fn map_w() -> Func {
    rec(
        "map_w",
        vec!["l"],
        iff(
            is_nil(var("l")),
            var("l"),
            prepend(add(head(var("l")), int(1)), call("map_w", vec![tail(var("l"))])),
        ),
    )
}

fn map_index(n: usize) -> Program {
    Program {
        funcs: vec![chk_i(), build_i(), map_i()],
        main: sum_i(call("map_i", vec![built_i(n), int(n as i64), int(0)]), n),
    }
}

fn map_walk(n: usize) -> Program {
    Program {
        funcs: vec![chk_w(), build_w(), map_w()],
        main: sum_w(call("map_w", vec![built_w(n)])),
    }
}

// --- 4. reverse ------------------------------------------------------------

/// The moves-last helper: its list parameter comes after the element that
/// has to be read before the first write lands.
fn swap_() -> Func {
    func("swap_", vec!["a", "j", "l2"], set(var("l2"), var("a"), var("j")))
}

/// `rev_i(l, i, j)` — reverse by swapping ends inwards.
fn rev_i() -> Func {
    rec(
        "rev_i",
        vec!["l", "i", "j"],
        iff(
            lt(var("i"), var("j")),
            call(
                "rev_i",
                vec![
                    call(
                        "swap_",
                        vec![
                            get(var("l"), var("i")),
                            var("j"),
                            set(var("l"), get(var("l"), var("j")), var("i")),
                        ],
                    ),
                    add(var("i"), int(1)),
                    sub(var("j"), int(1)),
                ],
            ),
            var("l"),
        ),
    )
}

/// `rev_w(l, acc)` — the textbook accumulator reverse.
fn rev_w() -> Func {
    rec(
        "rev_w",
        vec!["l", "acc"],
        iff(
            is_nil(var("l")),
            var("acc"),
            call("rev_w", vec![tail(var("l")), prepend(head(var("l")), var("acc"))]),
        ),
    )
}

fn reverse_index(n: usize) -> Program {
    Program {
        funcs: vec![chk_i(), build_i(), swap_(), rev_i()],
        main: sum_i(call("rev_i", vec![built_i(n), int(0), int(n as i64 - 1)]), n),
    }
}

fn reverse_walk(n: usize) -> Program {
    Program {
        funcs: vec![chk_w(), build_w(), rev_w()],
        main: sum_w(call("rev_w", vec![built_w(n), nil()])),
    }
}

// --- 5. scatter ------------------------------------------------------------

/// `scat(l, n, i, k)` — k updates at scattered positions.
fn scat() -> Func {
    rec(
        "scat",
        vec!["l", "n", "i", "k"],
        iff(
            eq(var("i"), var("k")),
            var("l"),
            call(
                "scat",
                vec![
                    set(var("l"), var("i"), rem(mul(var("i"), int(STRIDE)), var("n"))),
                    var("n"),
                    add(var("i"), int(1)),
                    var("k"),
                ],
            ),
        ),
    )
}

fn scatter_index(n: usize) -> Program {
    let scattered = call("scat", vec![built_i(n), int(n as i64), int(0), int(n as i64)]);
    Program { funcs: vec![chk_i(), build_i(), scat()], main: sum_i(scattered, n) }
}

fn scatter_walk(n: usize) -> Program {
    let scattered = call("scat", vec![built_w(n), int(n as i64), int(0), int(n as i64)]);
    Program { funcs: vec![chk_w(), build_w(), scat()], main: sum_w(scattered) }
}

// --- 6. fork ---------------------------------------------------------------

/// `fork(base, m, j, acc, idx)` — m independent versions of one shared list,
/// each differing from it at `idx`. The base stays live, so the update can
/// never be in place.
fn fork() -> Func {
    rec(
        "fork",
        vec!["base", "m", "j", "acc", "idx"],
        iff(
            eq(var("j"), var("m")),
            var("acc"),
            call(
                "fork",
                vec![
                    var("base"),
                    var("m"),
                    add(var("j"), int(1)),
                    chk(var("acc"), get(set(var("base"), var("j"), var("idx")), var("idx"))),
                    var("idx"),
                ],
            ),
        ),
    )
}

fn fork_main(l: Expr, n: usize, idx: i64) -> Expr {
    call("fork", vec![l, int(n as i64), int(0), int(0), int(idx)])
}

fn fork_head_index(n: usize) -> Program {
    Program { funcs: vec![build_i(), fork()], main: fork_main(built_i(n), n, 0) }
}

fn fork_head_walk(n: usize) -> Program {
    Program { funcs: vec![build_w(), fork()], main: fork_main(built_w(n), n, 0) }
}

fn fork_last_index(n: usize) -> Program {
    Program { funcs: vec![build_i(), fork()], main: fork_main(built_i(n), n, n as i64 - 1) }
}

fn fork_last_walk(n: usize) -> Program {
    Program { funcs: vec![build_w(), fork()], main: fork_main(built_w(n), n, n as i64 - 1) }
}

// --- 7. garbage ------------------------------------------------------------

fn temp4() -> Expr {
    list(vec![var("i"), add(var("i"), int(1)), add(var("i"), int(2)), add(var("i"), int(3))])
}

fn projection(t: &'static str) -> Expr {
    list(vec![get(var(t), int(0)), get(var(t), int(3))])
}

/// One four-element temporary per iteration, of which a two-element
/// projection survives. The temporary dies in the caller's frame.
fn garbage_index(n: usize) -> Program {
    let proj = func("proj", vec!["t", "acc"], push(var("acc"), projection("t")));
    let gar = rec(
        "gar",
        vec!["acc", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("acc"),
            call(
                "gar",
                vec![call("proj", vec![temp4(), var("acc")]), var("n"), add(var("i"), int(1))],
            ),
        ),
    );
    let built = call("gar", vec![nil(), int(n as i64), int(0)]);
    Program {
        funcs: vec![pair_sum(), chkp_i(), proj, gar],
        main: call("chkp_i", vec![built, int(n as i64), int(0), int(0)]),
    }
}

fn garbage_walk(n: usize) -> Program {
    let proj = func("proj_w", vec!["t", "acc"], prepend(projection("t"), var("acc")));
    let gar = rec(
        "gar_w",
        vec!["acc", "i"],
        iff(
            lt(var("i"), int(0)),
            var("acc"),
            call("gar_w", vec![call("proj_w", vec![temp4(), var("acc")]), sub(var("i"), int(1))]),
        ),
    );
    let built = call("gar_w", vec![nil(), int(n as i64 - 1)]);
    Program {
        funcs: vec![pair_sum(), chkp_w(), proj, gar],
        main: call("chkp_w", vec![built, int(0)]),
    }
}

// --- 8. nested -------------------------------------------------------------

fn pair_at() -> Expr {
    list(vec![var("i"), mul(var("i"), int(2))])
}

fn nested_index(n: usize) -> Program {
    let pairs = rec(
        "pairs_i",
        vec!["l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call("pairs_i", vec![push(var("l"), pair_at()), var("n"), add(var("i"), int(1))]),
        ),
    );
    let built = call("pairs_i", vec![nil(), int(n as i64), int(0)]);
    Program {
        funcs: vec![pair_sum(), chkp_i(), pairs],
        main: call("chkp_i", vec![built, int(n as i64), int(0), int(0)]),
    }
}

fn nested_walk(n: usize) -> Program {
    let pairs = rec(
        "pairs_w",
        vec!["l", "i"],
        iff(
            lt(var("i"), int(0)),
            var("l"),
            call("pairs_w", vec![prepend(pair_at(), var("l")), sub(var("i"), int(1))]),
        ),
    );
    let built = call("pairs_w", vec![nil(), int(n as i64 - 1)]);
    Program { funcs: vec![pair_sum(), chkp_w(), pairs], main: call("chkp_w", vec![built, int(0)]) }
}

/// A diagnostic, not a realistic task: the *same* pair, created before the
/// list, is pushed n times. The element is one slot and points below the
/// list, so nothing forces a copy — which isolates why `nested` above cannot
/// stay in place.
fn nested_old_index(n: usize) -> Program {
    let fill = rec(
        "fill",
        vec!["p", "l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call("fill", vec![var("p"), push(var("l"), var("p")), var("n"), add(var("i"), int(1))]),
        ),
    );
    let built = call("fill", vec![list(vec![int(3), int(4)]), nil(), int(n as i64), int(0)]);
    Program {
        funcs: vec![pair_sum(), chkp_i(), fill],
        main: call("chkp_i", vec![built, int(n as i64), int(0), int(0)]),
    }
}

/// The `nested` job written by consing: each fresh pair is put on top of the
/// chain and pointed *down* at, which is the one thing a flat list cannot do
/// with an element younger than itself.
fn nested_pairs(n: usize) -> Program {
    let chkp_p = rec(
        "chkp_p",
        vec!["l", "acc"],
        iff(
            pnil(var("l")),
            var("acc"),
            call(
                "chkp_p",
                vec![pcdr(var("l")), chk(var("acc"), call("pair_sum", vec![pcar(var("l"))]))],
            ),
        ),
    );
    let pairs_p = rec(
        "pairs_p",
        vec!["l", "i"],
        iff(
            lt(var("i"), int(0)),
            var("l"),
            call("pairs_p", vec![pcons(pair_at(), var("l")), sub(var("i"), int(1))]),
        ),
    );
    let built = call("pairs_p", vec![nil(), int(n as i64 - 1)]);
    Program { funcs: vec![pair_sum(), chkp_p, pairs_p], main: call("chkp_p", vec![built, int(0)]) }
}

// --- 9. tree ---------------------------------------------------------------

/// Non-tail recursion whose result is a compound value: every return escapes
/// the frame that built it.
fn tree(depth: usize) -> Program {
    let mk = rec(
        "mk",
        vec!["d"],
        iff(
            eq(var("d"), int(0)),
            list(vec![int(1)]),
            list(vec![
                call("mk", vec![sub(var("d"), int(1))]),
                call("mk", vec![sub(var("d"), int(1))]),
            ]),
        ),
    );
    let tsum = rec(
        "tsum",
        vec!["t"],
        iff(
            eq(len(var("t")), int(1)),
            get(var("t"), int(0)),
            add(
                call("tsum", vec![get(var("t"), int(0))]),
                call("tsum", vec![get(var("t"), int(1))]),
            ),
        ),
    );
    Program { funcs: vec![mk, tsum], main: call("tsum", vec![call("mk", vec![int(depth as i64)])]) }
}

fn leaves(depth: usize) -> usize {
    1 << depth
}

// --- 10. drain -------------------------------------------------------------

/// `drain_i(acc, l, n)` — take the last element, then drop it. The
/// accumulator comes first so the read happens before the move.
fn drain_i() -> Func {
    rec(
        "drain_i",
        vec!["acc", "l", "n"],
        iff(
            eq(var("n"), int(0)),
            var("acc"),
            call(
                "drain_i",
                vec![
                    add(var("acc"), get(var("l"), sub(var("n"), int(1)))),
                    pop_last(var("l")),
                    sub(var("n"), int(1)),
                ],
            ),
        ),
    )
}

fn drain_w() -> Func {
    rec(
        "drain_w",
        vec!["acc", "l"],
        iff(
            is_nil(var("l")),
            var("acc"),
            call("drain_w", vec![add(var("acc"), head(var("l"))), tail(var("l"))]),
        ),
    )
}

fn drain_index(n: usize) -> Program {
    Program {
        funcs: vec![build_i(), drain_i()],
        main: call("drain_i", vec![int(0), built_i(n), int(n as i64)]),
    }
}

fn drain_walk(n: usize) -> Program {
    Program { funcs: vec![build_w(), drain_w()], main: call("drain_w", vec![int(0), built_w(n)]) }
}

// --- 11. selection sort ----------------------------------------------------

/// A shuffled list: `i * STRIDE mod n` is a permutation of 0..n.
fn shuffled_i() -> Func {
    rec(
        "shuf_i",
        vec!["l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call(
                "shuf_i",
                vec![
                    push(var("l"), rem(mul(var("i"), int(STRIDE)), var("n"))),
                    var("n"),
                    add(var("i"), int(1)),
                ],
            ),
        ),
    )
}

fn shuffled_w() -> Func {
    rec(
        "shuf_w",
        vec!["l", "n", "i"],
        iff(
            lt(var("i"), int(0)),
            var("l"),
            call(
                "shuf_w",
                vec![
                    prepend(rem(mul(var("i"), int(STRIDE)), var("n")), var("l")),
                    var("n"),
                    sub(var("i"), int(1)),
                ],
            ),
        ),
    )
}

fn sort_funcs() -> Vec<Func> {
    let argmin = rec(
        "argmin",
        vec!["l", "n", "j", "best"],
        iff(
            eq(var("j"), var("n")),
            var("best"),
            call(
                "argmin",
                vec![
                    var("l"),
                    var("n"),
                    add(var("j"), int(1)),
                    iff(
                        lt(get(var("l"), var("j")), get(var("l"), var("best"))),
                        var("j"),
                        var("best"),
                    ),
                ],
            ),
        ),
    );
    let swap = func(
        "swap",
        vec!["l", "i", "j"],
        call(
            "swap_",
            vec![
                get(var("l"), var("i")),
                var("j"),
                set(var("l"), get(var("l"), var("j")), var("i")),
            ],
        ),
    );
    let sel = rec(
        "sel",
        vec!["l", "n", "i"],
        iff(
            eq(var("i"), var("n")),
            var("l"),
            call(
                "sel",
                vec![
                    call(
                        "swap",
                        vec![
                            var("l"),
                            var("i"),
                            call(
                                "argmin",
                                vec![var("l"), var("n"), add(var("i"), int(1)), var("i")],
                            ),
                        ],
                    ),
                    var("n"),
                    add(var("i"), int(1)),
                ],
            ),
        ),
    );
    vec![swap_(), argmin, swap, sel]
}

fn sort_index(n: usize) -> Program {
    let mut funcs = vec![chk_i(), shuffled_i()];
    funcs.extend(sort_funcs());
    let shuffled = call("shuf_i", vec![nil(), int(n as i64), int(0)]);
    let sorted = call("sel", vec![shuffled, int(n as i64), int(0)]);
    Program { funcs, main: sum_i(sorted, n) }
}

fn sort_walk(n: usize) -> Program {
    let mut funcs = vec![chk_w(), shuffled_w()];
    funcs.extend(sort_funcs());
    let shuffled = call("shuf_w", vec![nil(), int(n as i64), int(n as i64 - 1)]);
    let sorted = call("sel", vec![shuffled, int(n as i64), int(0)]);
    Program { funcs, main: sum_w(sorted) }
}

// --- 0. baseline ----------------------------------------------------------

/// No lists at all: `count(n, acc) = if n == 0 { acc } else { count(n-1, acc+n) }`.
/// The floor cost of a tail-recursive loop on each VM, so the list tasks can
/// be read as "this much on top of the interpreter".
fn baseline(n: usize) -> Program {
    let count = rec(
        "count",
        vec!["n", "acc"],
        iff(
            eq(var("n"), int(0)),
            var("acc"),
            call("count", vec![sub(var("n"), int(1)), add(var("acc"), var("n"))]),
        ),
    );
    Program { funcs: vec![count], main: call("count", vec![int(n as i64), int(0)]) }
}

// --- the suite -------------------------------------------------------------

fn task(
    name: &'static str,
    about: &'static str,
    sizes: &'static [usize],
    variants: Vec<Variant>,
) -> Task {
    Task { name, about, unit: "elem", elems: ident, sizes, variants }
}

fn both(index: fn(usize) -> Program, walk: fn(usize) -> Program) -> Vec<Variant> {
    vec![Variant { idiom: "index", build: index }, Variant { idiom: "walk", build: walk }]
}

pub fn suite() -> Vec<Task> {
    vec![
        Task {
            name: "loop",
            about: "a tail-recursive counting loop with no lists at all (interpreter floor)",
            unit: "iter",
            elems: ident,
            sizes: &[1024, 4096],
            variants: vec![Variant { idiom: "-", build: baseline }],
        },
        task(
            "build",
            "grow a list to n elements one at a time, then checksum it",
            &[1024, 4096],
            vec![
                Variant { idiom: "index", build: build_index },
                Variant { idiom: "walk", build: build_walk },
                Variant { idiom: "pairs", build: build_pairs },
            ],
        ),
        task(
            "random_access",
            "n reads at scattered indices",
            &[1024, 4096],
            both(random_index, random_walk),
        ),
        task(
            "map",
            "add 1 to every element, then checksum",
            &[16, 64, 1024, 4096],
            vec![
                Variant { idiom: "index", build: map_index },
                Variant { idiom: "walk", build: map_walk },
                Variant { idiom: "pairs", build: map_pairs },
            ],
        ),
        task(
            "reverse",
            "reverse the list, then checksum",
            &[1024, 4096],
            both(reverse_index, reverse_walk),
        ),
        task(
            "scatter",
            "n single-element updates at scattered indices",
            &[1024, 4096],
            both(scatter_index, scatter_walk),
        ),
        task(
            "fork_head",
            "n versions of one shared list, each differing at element 0",
            &[512, 2048],
            vec![
                Variant { idiom: "index", build: fork_head_index },
                Variant { idiom: "walk", build: fork_head_walk },
                Variant { idiom: "pairs", build: fork_head_pairs },
            ],
        ),
        task(
            "fork_last",
            "n versions of one shared list, each differing at the last element",
            &[512, 2048],
            both(fork_last_index, fork_last_walk),
        ),
        task(
            "garbage",
            "one four-element temporary per element, a two-element projection kept",
            &[512, 2048],
            both(garbage_index, garbage_walk),
        ),
        task(
            "nested",
            "build a list of n pairs, then read both fields of each",
            &[1024, 4096],
            vec![
                Variant { idiom: "index", build: nested_index },
                Variant { idiom: "walk", build: nested_walk },
                Variant { idiom: "pairs", build: nested_pairs },
            ],
        ),
        task(
            "nested_shared",
            "push one pair, created before the list, n times (diagnostic)",
            &[1024, 4096],
            vec![Variant { idiom: "index", build: nested_old_index }],
        ),
        Task {
            name: "tree",
            about: "build a balanced binary tree of depth d, then sum its leaves",
            unit: "leaf",
            elems: leaves,
            sizes: &[10, 12],
            variants: vec![Variant { idiom: "-", build: tree }],
        },
        task(
            "drain",
            "remove and sum every element, one at a time",
            &[1024, 4096],
            both(drain_index, drain_walk),
        ),
        task(
            "sort",
            "selection sort of a shuffled list, then checksum",
            &[128, 512],
            both(sort_index, sort_walk),
        ),
    ]
}
