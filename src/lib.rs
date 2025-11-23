use std::{
    collections::{BTreeMap, HashSet},
    iter,
    rc::Rc,
    vec::IntoIter,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'code> {
    Num(usize),
    Ident(&'code str),
    String(&'code str),
    Keyword(&'code str),
    LParen,
    RParen,
    Colon,
    Comma,
    DoubleEq,
    Ampersand,
}

impl std::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("'")?;
        match self {
            Tok::Num(n) => write!(f, "{n}"),
            Tok::Keyword(s) | Tok::Ident(s) => f.write_str(s),
            Tok::String(s) => write!(f, "'{s}'"),
            Tok::LParen => f.write_str("("),
            Tok::RParen => f.write_str(")"),
            Tok::Colon => f.write_str(":"),
            Tok::Comma => f.write_str(","),
            Tok::DoubleEq => f.write_str("=="),
            Tok::Ampersand => f.write_str("&"),
        }?;
        f.write_str("'")
    }
}

fn scan(code: &str) -> Vec<(Tok<'_>, usize)> {
    let mut toks = vec![];
    let mut i = 0;
    let mut chars = code.char_indices().chain(iter::once((code.len(), ' ')));
    while let Some((j, c)) = chars.next() {
        let tok = match c {
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            ':' => Some(Tok::Colon),
            ',' => Some(Tok::Comma),
            _ => None,
        };
        let is_comment = c == '#';
        let is_str_literal = c == '\'';
        if tok.is_some() || c.is_whitespace() || is_comment || is_str_literal {
            if !code[i..j].is_empty() {
                let tok = match &code[i..j] {
                    "==" => Tok::DoubleEq,
                    "&" => Tok::Ampersand,
                    kw @ ("if" | "else") => Tok::Keyword(kw),
                    _ => match &code[i..j].parse::<usize>() {
                        Ok(n) => Tok::Num(*n),
                        Err(_) => Tok::Ident(&code[i..j]),
                    },
                };
                toks.push((tok, i));
            }
            i = j + 1;
        }
        if let Some(tok) = tok {
            toks.push((tok, j));
        } else if is_comment {
            let (j, _) = chars.find(|(_, c)| *c == '\n').unwrap_or_default();
            i = j + 1;
        } else if is_str_literal {
            let s = chars.by_ref().take_while(|(_, c)| *c != '\'').count();
            toks.push((Tok::String(&code[j + 1..j + 1 + s]), i));
            i = j + s + 2;
        }
    }
    toks
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Expr {
    Var(String),
    String(String),
    Eq([Box<Expr>; 2]),
    TimeLoop(Vec<(Expr, Expr)>),
    Lambda(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

fn pos_at(i: usize, code: &str) -> String {
    let (mut line, mut col) = (1, 1);
    for c in code.chars().take(i) {
        if c == '\n' {
            line += 1;
            col = 0;
        }
        col += 1;
    }
    format!("line {line}, col {col}")
}

fn parse(code: &str) -> Result<Expr, String> {
    type Toks<'c> = iter::Peekable<IntoIter<(Tok<'c>, usize)>>;
    fn expect(toks: &mut Toks<'_>, t: Tok<'_>) -> Result<(), (String, Option<usize>)> {
        match toks.next() {
            Some((tok, _)) if tok == t => Ok(()),
            Some((tok, i)) => Err((format!("Expected {t}, but found {tok}"), Some(i))),
            None => Err((format!("Expected {t}, but the code just ended"), None)),
        }
    }
    fn parse_expr(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        match toks.peek() {
            Some((Tok::Keyword("if"), _)) => {
                toks.next();
                let p = parse_infix(toks)?;
                expect(toks, Tok::Colon)?;
                let t = parse_expr(toks)?;
                expect(toks, Tok::Keyword("else"))?;
                expect(toks, Tok::Colon)?;
                let f = parse_expr(toks)?;
                Ok(Expr::App(
                    Box::new(Expr::App(Box::new(p), Box::new(t))),
                    Box::new(f),
                ))
            }
            _ => parse_infix(toks),
        }
    }
    fn parse_infix(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        let x = parse_arg(toks)?;
        match toks.peek() {
            Some((Tok::DoubleEq, _)) => {
                toks.next();
                let y = parse_arg(toks)?;
                Ok(Expr::Eq([Box::new(x), Box::new(y)]))
            }
            _ => Ok(x),
        }
    }
    fn parse_arg(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        let Some((tok, i)) = toks.next() else {
            return Err(("Expected an expression, but found nothing".into(), None));
        };
        match tok {
            Tok::Ident(v) => Ok(Expr::Var(v.into())),
            Tok::String(s) => Ok(Expr::String(s.into())),
            Tok::LParen => {
                let expr = parse_expr(toks)?;
                if let Some((Tok::Colon, _)) = toks.peek() {
                    toks.next();
                    let v = parse_expr(toks)?;
                    let mut exprs = vec![(expr, v)];
                    while let Some((Tok::Comma, _)) = toks.peek() {
                        toks.next();
                        let k = parse_expr(toks)?;
                        expect(toks, Tok::Colon)?;
                        let v = parse_expr(toks)?;
                        exprs.push((k, v))
                    }
                    expect(toks, Tok::RParen)?;
                    Ok(Expr::TimeLoop(exprs))
                } else {
                    let mut exprs = vec![expr];
                    while let Some((Tok::Ampersand, _)) = toks.peek() {
                        toks.next();
                        exprs.push(parse_expr(toks)?);
                    }
                    expect(toks, Tok::RParen)?;
                    if exprs.len() == 1 {
                        Ok(exprs.pop().unwrap())
                    } else {
                        Ok(Expr::TimeLoop(
                            exprs.into_iter().map(|v| (v.clone(), v)).collect(),
                        ))
                    }
                }
            }
            Tok::RParen
            | Tok::Colon
            | Tok::Comma
            | Tok::DoubleEq
            | Tok::Ampersand
            | Tok::Num(_)
            | Tok::Keyword(_) => Err((format!("Expected an expression, found {tok}"), Some(i))),
        }
    }
    let mut toks = scan(code).into_iter().peekable();
    match parse_expr(&mut toks) {
        Ok(expr) => match toks.next() {
            Some((tok, i)) => Err(format!(
                "Expected the code to end, but found {tok} at {}",
                pos_at(i, code)
            )),
            None => Ok(expr),
        },
        Err((e, Some(i))) => Err(format!("{e} at {}", pos_at(i, code))),
        Err((e, None)) => Err(e),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Env {
    Nil,
    Entry(String, Val, Rc<Env>),
}

impl Env {
    fn set(self: &Rc<Self>, k: String, v: Val) -> Rc<Env> {
        Rc::new(Env::Entry(k, v, Rc::clone(&self)))
    }

    fn get(&self, var: &str) -> Result<&Val, String> {
        match self {
            Env::Nil => Err(format!("Unbound variable {var}")),
            Env::Entry(k, val, _) if k == var => Ok(val),
            Env::Entry(_, _, env) => env.get(var),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Val {
    String(String),
    Lambda(String, Box<Expr>, Rc<Env>),
    TimeLoop(BTreeMap<Val, Val>),
}

impl Val {
    fn time_loop(l: BTreeMap<Val, Val>) -> Val {
        simplify(Val::TimeLoop(l))
    }
}

fn is_loop(l: &BTreeMap<Val, Val>) -> bool {
    l.keys().collect::<HashSet<_>>() == l.values().collect::<HashSet<_>>()
}

fn normalize(l: BTreeMap<Val, Val>) -> BTreeMap<Val, Val> {
    let mut normalized = BTreeMap::new();
    for (mut k, mut v) in l.into_iter() {
        if let Val::TimeLoop(l) = k {
            k = Val::TimeLoop(normalize(l));
        }
        if let Val::TimeLoop(l) = v {
            v = Val::TimeLoop(normalize(l));
        }
        normalized.insert(k, v);
    }
    if is_loop(&normalized) {
        normalized
            .into_iter()
            .map(|(k, _)| (k.clone(), k))
            .collect()
    } else {
        normalized
    }
}

fn simplify(v: Val) -> Val {
    match v {
        Val::TimeLoop(l) => {
            let l: BTreeMap<_, _> = l
                .into_iter()
                .map(|(k, v)| (simplify(k), simplify(v)))
                .collect();
            match l.values().collect::<HashSet<_>>().len() {
                1 => l.into_iter().map(|(_, v)| v).next().unwrap(),
                _ => Val::TimeLoop(l),
            }
        }
        _ => v,
    }
}

impl Val {
    fn rank(&self) -> usize {
        match self {
            Val::String(_) | Val::Lambda(_, _, _) => 0,
            Val::TimeLoop(vals) => {
                vals.iter()
                    .map(|(k, _v)| k.rank())
                    .max()
                    .unwrap_or_default()
                    + 1
            }
        }
    }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::String(s) => write!(f, "'{s}'"),
            Val::TimeLoop(vals) => {
                f.write_str("(")?;
                let is_loop = is_loop(&vals);
                for (i, (k, v)) in vals.iter().enumerate() {
                    if i != 0 {
                        if is_loop {
                            f.write_str(" & ")?;
                        } else {
                            f.write_str(", ")?;
                        }
                    }
                    if is_loop {
                        write!(f, "{v}")?;
                    } else {
                        write!(f, "{k}: {v}")?;
                    }
                }
                f.write_str(")")
            }
            Val::Lambda(param, body, env) => {
                write!(f, "{param} => {body:?}@{env:?}")
            }
        }
    }
}

fn eq(a: Val, b: Val) -> Result<Val, String> {
    fn _true() -> Val {
        Val::Lambda(
            "x".into(),
            Box::new(Expr::Lambda("y".into(), Box::new(Expr::Var("x".into())))),
            Rc::new(Env::Nil),
        )
    }
    fn _false() -> Val {
        Val::Lambda(
            "x".into(),
            Box::new(Expr::Lambda("y".into(), Box::new(Expr::Var("y".into())))),
            Rc::new(Env::Nil),
        )
    }
    let rank_a = a.rank();
    let rank_b = b.rank();
    match (a, b) {
        (Val::String(a), Val::String(b)) if a == b => Ok(_true()),
        (Val::String(_), Val::String(_)) => Ok(_false()),
        (a @ Val::Lambda(_, _, _), b) | (a, b @ Val::Lambda(_, _, _)) => {
            Err(format!("Cannot compare {a} with {b}"))
        }
        (a, Val::TimeLoop(b)) if rank_a < rank_b => {
            let mut compared = BTreeMap::new();
            for (k, v) in b {
                compared.insert(k.clone(), eq(a.clone(), v)?);
            }
            Ok(Val::time_loop(compared))
        }
        (Val::TimeLoop(a), b) if rank_a > rank_b => {
            let mut compared = BTreeMap::new();
            for (k, v) in a {
                compared.insert(k.clone(), eq(v, b.clone())?);
            }
            Ok(Val::time_loop(compared))
        }
        (Val::TimeLoop(mut a), Val::TimeLoop(mut b)) => {
            a = normalize(a);
            b = normalize(b);
            let mut compared = BTreeMap::new();
            for (k, a) in a {
                if let Some(b) = b.remove(&k) {
                    compared.insert(k, eq(a, b)?);
                }
            }
            Ok(Val::time_loop(compared))
        }
        (Val::String(_), Val::TimeLoop(_)) | (Val::TimeLoop(_), Val::String(_)) => unreachable!(),
    }
}

fn app(f: Val, arg: Val) -> Result<Val, String> {
    let rank_f = f.rank();
    let rank_arg = arg.rank();
    match f {
        Val::String(s) => Err(format!("Cannot apply the string {s} to the argument {arg}")),
        Val::Lambda(param, body, env) => body.eval(&env.set(param, arg)),
        Val::TimeLoop(f) => match arg {
            Val::TimeLoop(mut arg) if rank_f == rank_arg => {
                let mut zipped = BTreeMap::new();
                for (k, f) in f.into_iter() {
                    if let Some(arg) = arg.remove(&k) {
                        zipped.insert(k, app(f, arg)?);
                    }
                }
                Ok(Val::time_loop(zipped))
            }
            Val::TimeLoop(arg) if rank_f < rank_arg => {
                let mut mapped = BTreeMap::new();
                for (k, arg) in arg {
                    mapped.insert(k, app(Val::TimeLoop(f.clone()), arg)?);
                }
                Ok(Val::time_loop(mapped))
            }
            arg => {
                let mut mapped = BTreeMap::new();
                for (k, f) in f {
                    mapped.insert(k, app(f, arg.clone())?);
                }
                Ok(Val::time_loop(mapped))
            }
        },
    }
}

impl Expr {
    fn eval(self, env: &Rc<Env>) -> Result<Val, String> {
        match self {
            Expr::Var(v) => env.get(&v).cloned(),
            Expr::String(s) => Ok(Val::String(s)),
            Expr::Eq([a, b]) => {
                let a = a.eval(env)?;
                let b = b.eval(env)?;
                eq(a, b)
            }
            Expr::TimeLoop(vals) => {
                let mut evaled = BTreeMap::new();
                for (k, v) in vals {
                    let k = k.eval(env)?;
                    let v = v.eval(env)?;
                    evaled.insert(k, v);
                }
                Ok(Val::time_loop(evaled))
            }
            Expr::Lambda(v, body) => Ok(Val::Lambda(v, body, Rc::clone(env))),
            Expr::App(f, arg) => {
                let f = f.eval(env)?;
                let arg = arg.eval(env)?;
                app(f, arg)
            }
        }
    }
}

pub fn eval(code: &str) -> Result<String, String> {
    let expr = parse(code)?;
    let val = match expr.eval(&Rc::new(Env::Nil))? {
        Val::TimeLoop(l) => Val::time_loop(normalize(l)),
        v => v,
    };
    Ok(format!("{val}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_idiot1() -> Result<(), String> {
        let v = "'x'";
        let code = format!(
            "
        if {v} == 'x':
            'x'
        else:
            'y'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn simple_idiot2() -> Result<(), String> {
        let v = "'y'";
        let code = format!(
            "
        if {v} == 'x':
            'x'
        else:
            'y'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn simple_liar() -> Result<(), String> {
        let v = "('x' & 'y')";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn captured_liar() -> Result<(), String> {
        let v = "('y' & ('x' & 'y'))";
        let code = format!(
            "
        if {v} == ('x' & 'y'):
            'y'
        else:
            'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar1() -> Result<(), String> {
        let v = "('x' & ('x' & 'y'))";
        let code = format!(
            "
        if {v} == ('x' & 'y'):
            'x'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar2() -> Result<(), String> {
        let v = "('y' & ('x' & 'y'))";
        let code = format!(
            "
        if {v} == ('x' & 'y'):
            'y'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar3() -> Result<(), String> {
        // 'x' -> ('x': 'z', 'y': 'y')
        // ('x': 'z', 'y': 'y') -> ('x': 'x', 'y': 'z')
        // ('x': 'x', 'y': 'z') -> ('x': 'z', 'y': 'x')
        // ('x': 'z', 'y': 'x') -> ('x' & 'y')
        // ('x' & 'y') -> 'z'
        // 'z' -> 'x'
        let v = "('x' & 'z' & ('x' & 'y') & ('x': 'x', 'y': 'z') & ('x': 'z', 'y': 'x') & ('x': 'z', 'y': 'y'))";
        let code = format!(
            "
        if {v} == ('x' & 'y'):
            'z'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn liar_twin1() -> Result<(), String> {
        let v = "('x' & 'y')";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn liar_twin2() -> Result<(), String> {
        let v = "('x' & 'y')";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            if {v} == 'x':
                'z'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }
}
