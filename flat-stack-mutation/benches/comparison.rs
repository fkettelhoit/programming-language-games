//! Flat stack mutation vs. a traditional cons-cell VM.
//!
//! Run with `cargo bench --bench comparison`. Add `--` and a task name to
//! run one task, or `-- --quick` to skip the largest size of each.

mod harness;

use std::collections::BTreeMap;

use harness::run::{Backend, Measure, profile_flat, run};
use harness::tasks::{Task, backends_for, suite};

struct Row {
    idiom: &'static str,
    backend: Backend,
    m: Measure,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let quick = args.iter().any(|a| a == "--quick");
    let filters: Vec<&str> =
        args.iter().filter(|a| !a.starts_with("--")).map(|s| s.as_str()).collect();

    if let Some(i) = args.iter().position(|a| a == "--ops") {
        let task = args.get(i + 1).map(|s| s.as_str()).unwrap_or("loop");
        ops_profile(task);
        return;
    }

    header();
    let mut summary: Vec<(String, String)> = vec![];
    for task in suite() {
        if !filters.is_empty() && !filters.iter().any(|f| task.name.contains(f)) {
            continue;
        }
        let sizes: Vec<usize> = if quick { task.sizes[..1].to_vec() } else { task.sizes.to_vec() };
        summary.extend(report(&task, &sizes));
    }

    println!("\n\n## Summary — work per element, best program per model\n");
    println!("{:<16}  detail", "task");
    println!("{}", "-".repeat(78));
    for (task, line) in summary {
        println!("{task:<16}  {line}");
    }
}

fn args_idiom() -> Option<String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let i = args.iter().position(|a| a == "--ops")?;
    args.get(i + 2).cloned()
}

/// Where the flat VM spends its work on one program, per kind of op.
fn ops_profile(name: &str) {
    let Some(task) = suite().into_iter().find(|t| t.name.contains(name)) else {
        println!("no task matching {name:?}");
        return;
    };
    let idiom = args_idiom();
    let v = task
        .variants
        .iter()
        .find(|v| idiom.as_deref().is_none_or(|i| v.idiom == i))
        .unwrap_or(&task.variants[0]);
    let n = task.sizes[0];
    let prog = (v.build)(n);
    let rows = profile_flat(&prog).expect("runs");
    let total: usize = rows.iter().map(|(_, _, w)| w).sum();
    let steps: usize = rows.iter().map(|(_, c, _)| c).sum();
    println!("flat VM work by op — {} / {} at n={n}\n", task.name, v.idiom);
    println!("  {:<18} {:>9} {:>12} {:>9} {:>7}", "op", "executed", "work", "work/op", "share");
    for (label, count, work) in &rows {
        println!(
            "  {:<18} {:>9} {:>12} {:>9.1} {:>6.1}%",
            label,
            count,
            work,
            *work as f64 / *count as f64,
            100.0 * *work as f64 / total as f64,
        );
    }
    println!("  {:<18} {steps:>9} {total:>12}", "total");
}

fn header() {
    println!("# flat-stack-mutation vs. a cons-cell VM\n");
    println!("Backends:");
    println!("  flat         the experiment; last-use moves let the in-place paths fire");
    println!("  flat-shared  the same program with every operand borrowed (copy-on-write)");
    println!("  cons         cons cells, reference counted, persistent update");
    println!("  cons-reuse   cons cells, reference counted, in-place when the count is 1");
    println!();
    println!("Idioms:");
    println!("  index        get/set/push/pop_last — the only vocabulary the flat VM has");
    println!("  walk         head/tail/prepend — how a cons language is actually written;");
    println!("               the flat VM has no primitive for either, so it cannot run these");
    println!();
    println!("work   slot and field reads + writes, counted the same way on both sides");
    println!("       (instruction fetch, operand traffic, list walks, reference counts,");
    println!("       compaction). Deterministic; this is the metric to trust.");
    println!("peak   peak live footprint in 8-byte words, program and call frames");
    println!("       included: flat = tape slots x 2, cons = live cells x 3 + operand");
    println!("       stack + bytecode.");
    println!("alloc  cells allocated (the flat VM never allocates: it has no heap).");
    println!("steps  VM instructions executed; w/step is work per instruction, which");
    println!("       separates \"more instructions\" from \"more memory traffic each\".");
    println!("time   fastest of up to 25 runs, in microseconds.");
}

fn report(task: &Task, sizes: &[usize]) -> Vec<(String, String)> {
    println!("\n\n## {} — {}\n", task.name, task.about);
    let mut summary = vec![];
    let mut work_by_row: BTreeMap<String, Vec<f64>> = BTreeMap::new();
    for &n in sizes {
        let mut rows = vec![];
        for v in &task.variants {
            let prog = (v.build)(n);
            for backend in backends_for(&prog) {
                // Once the moved program is itself quadratic, running it with
                // every operand borrowed on top of that costs minutes and
                // says nothing new.
                if backend == Backend::FlatShared
                    && rows
                        .iter()
                        .any(|r: &Row| r.backend == Backend::Flat && r.m.work() > 10_000_000)
                {
                    continue;
                }
                match run(&prog, backend, true) {
                    Ok(m) => rows.push(Row { idiom: v.idiom, backend, m }),
                    Err(e) => println!("  !! {} {} n={n}: {e}", v.idiom, backend.label()),
                }
            }
        }
        let answers: Vec<i64> = rows.iter().map(|r| r.m.answer).collect();
        let agree = answers.windows(2).all(|w| w[0] == w[1]);
        let elems = (task.elems)(n);
        println!(
            "  n = {n} ({elems} {}s)   result {} {}",
            task.unit,
            answers.first().copied().unwrap_or(0),
            if agree { "(all backends agree)" } else { "!! BACKENDS DISAGREE !!" },
        );
        println!(
            "    {:<7} {:<12} {:>12} {:>9} {:>8} {:>6} {:>11} {:>10} {:>9}",
            "idiom",
            "backend",
            "work",
            "per/elem",
            "steps",
            "w/step",
            "peak(words)",
            "alloc",
            "time(us)"
        );
        for r in &rows {
            println!(
                "    {:<7} {:<12} {:>12} {:>9.1} {:>8} {:>6.1} {:>11} {:>10} {:>9.1}",
                r.idiom,
                r.backend.label(),
                r.m.work(),
                r.m.work() as f64 / elems as f64,
                r.m.steps,
                r.m.work() as f64 / r.m.steps as f64,
                r.m.words,
                r.m.allocs,
                r.m.nanos as f64 / 1000.0,
            );
            work_by_row
                .entry(format!("{:<7} {}", r.idiom, r.backend.label()))
                .or_default()
                .push(r.m.work() as f64 / elems as f64);
        }
        if n == *sizes.last().unwrap() {
            summary.push((task.name.to_string(), best_line(&rows, elems)));
        }
    }
    if sizes.len() > 1 {
        let (a, b) = (sizes[sizes.len() - 2], sizes[sizes.len() - 1]);
        println!("\n    growth of work from n={a} to n={b}:");
        let ratio = b as f64 / a as f64;
        for (label, ws) in &work_by_row {
            if ws.len() >= 2 {
                // per-element work ratio: 1 means linear, `ratio` means quadratic
                let g = ws[ws.len() - 1] / ws[ws.len() - 2];
                let shape = if g < 1.4 {
                    "linear"
                } else if g > ratio * 0.6 {
                    "quadratic"
                } else {
                    "in between"
                };
                println!("      {label:<20} per-element work x{g:>6.1}  ({shape})");
            }
        }
    }
    summary
}

fn best_line(rows: &[Row], elems: usize) -> String {
    let best = |f: fn(Backend) -> bool| -> Option<&Row> {
        rows.iter().filter(|r| f(r.backend)).min_by_key(|r| r.m.work())
    };
    let flat = best(|b| b == Backend::Flat);
    let cons = best(|b| !b.is_flat());
    match (flat, cons) {
        (Some(f), Some(c)) => {
            let fw = f.m.work() as f64 / elems as f64;
            let cw = c.m.work() as f64 / elems as f64;
            let (winner, factor) =
                if fw <= cw { ("flat", cw / fw) } else { (c.backend.label(), fw / cw) };
            format!(
                "flat {:>7.1}/elem, {} {:>7.1}/elem ({} {:.1}x)  |  peak {} vs {} words  |  alloc {}",
                fw,
                c.backend.label(),
                cw,
                winner,
                factor,
                f.m.words,
                c.m.words,
                c.m.allocs,
            )
        }
        _ => "—".to_string(),
    }
}
