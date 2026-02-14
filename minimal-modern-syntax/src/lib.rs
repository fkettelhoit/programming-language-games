#[derive(Debug, Clone, Copy)]
pub struct Pos(usize);

impl Pos {
    fn line_in(&self, code: &str) -> String {
        let (mut line, mut col) = (1, 1);
        for c in code.chars().take(self.0) {
            if c == '\n' {
                line += 1;
                col = 0;
            }
            col += 1;
        }
        format!("line {line}, col {col}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'code> {
    Sep(char),
    Var(&'code str),
    Key(&'code str),
    Str(&'code str),
}

impl std::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tok::Sep(c) => write!(f, "'{c}'"),
            Tok::Var(s) | Tok::Key(s) | Tok::Str(s) => write!(f, "'{s}'"),
        }
    }
}

fn scan(code: &str) -> Vec<(Pos, Tok<'_>)> {
    let mut toks = vec![];
    let mut i = 0;
    let mut chars = code
        .char_indices()
        .chain(std::iter::once((code.len(), ' ')));
    fn push_ident<'a>(toks: &mut Vec<(Pos, Tok<'a>)>, code: &'a str, i: usize, j: usize) {
        let s = &code[i..j];
        match s.chars().next() {
            None => {}
            Some(c) if c.is_ascii_uppercase() => toks.push((Pos(i), Tok::Str(s))),
            _ => toks.push((Pos(i), Tok::Var(s))),
        }
    }
    while let Some((j, c)) = chars.next() {
        match c {
            ':' if i < j => {
                toks.push((Pos(i), Tok::Key(&code[i..j])));
                i = j + 1;
            }
            '(' | ')' | '[' | ']' | '{' | '}' | '.' | ':' | ';' | ',' | '\n' => {
                push_ident(&mut toks, code, i, j);
                toks.push((Pos(j), Tok::Sep(c)));
                i = j + 1;
            }
            '/' if code.get(j + 1..j + 2) == Some("/") => {
                push_ident(&mut toks, code, i, j);
                i = chars
                    .by_ref()
                    .find(|(_, c)| *c == '\n')
                    .map_or(code.len(), |(j, _)| j + 1);
                toks.push((Pos(i), Tok::Sep('\n')));
            }
            '"' => {
                push_ident(&mut toks, code, i, j);
                i = chars
                    .by_ref()
                    .find(|(_, c)| *c == '"')
                    .map_or(code.len(), |(j, _)| j + 1);
                toks.push((Pos(j), Tok::Str(&code[j + 1..i - 1])));
            }
            c if c.is_ascii_whitespace() => {
                push_ident(&mut toks, code, i, j);
                i = j + 1;
            }
            _ => {}
        }
    }
    toks
}

#[derive(Debug, Clone)]
pub enum Ast<'code> {
    Var(Pos, &'code str),
    String(Pos, &'code str),
    List(Pos, Vec<Ast<'code>>),
    Tuple(Pos, Vec<Ast<'code>>),
    Block(Pos, Vec<Ast<'code>>),
    Prefix(Pos, Box<Ast<'code>>, Vec<Ast<'code>>),
    Infix(
        Pos,
        Box<Ast<'code>>,
        [Box<Ast<'code>>; 2],
        Option<Box<Ast<'code>>>,
    ),
}

struct Parser<'code> {
    end_pos: Pos,
    toks: std::iter::Peekable<std::vec::IntoIter<(Pos, Tok<'code>)>>,
}

impl<'c> Parser<'c> {
    fn expr(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        if let Some((i, Tok::Key(k))) = self.toks.peek().copied() {
            self.toks.next();
            return Ok(Ast::Tuple(
                i,
                vec![Ast::String(i, k), self.infix("value after key")?],
            ));
        }
        let (i, expr, mut args) = match self.infix(expected)? {
            Ast::Infix(i, f, [x, y], None) => match self.toks.peek().map(|(_, t)| t) {
                Some(Tok::Sep('[' | '{')) => {
                    let trailing = self.value("a trailing [...] or {...}")?;
                    return Ok(Ast::Infix(i, f, [x, y], Some(trailing.into())));
                }
                _ => return Ok(Ast::Infix(i, f, [x, y], None)),
            },
            Ast::Prefix(i, f, args) => (i, f, Some(args)),
            Ast::String(i, s) => (i, Box::new(Ast::String(i, s)), None),
            Ast::Var(i, v) => (i, Box::new(Ast::Var(i, v)), None),
            expr => return Ok(expr),
        };
        while let Some((_, Tok::Sep('[' | '{'))) = self.toks.peek() {
            args.get_or_insert_with(Vec::new)
                .push(self.value("a trailing [...] or {...}")?);
        }
        let mut kw_args = vec![];
        while let Some((i, Tok::Key(k))) = self.toks.peek().copied() {
            self.toks.next();
            kw_args.push(Ast::Tuple(
                i,
                vec![Ast::String(i, k), self.infix("a keyword argument")?],
            ));
        }
        if let Some(Ast::Tuple(i, _)) = kw_args.first() {
            args.get_or_insert_with(Vec::new)
                .push(Ast::List(*i, kw_args))
        }
        match args {
            None => Ok(*expr),
            Some(args) => Ok(Ast::Prefix(i, expr, args)),
        }
    }

    fn infix(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        let mut x = self.prefix(expected)?;
        let Some((i, Tok::Var(f))) = self.toks.peek().copied() else {
            return Ok(x);
        };
        x = match x {
            Ast::Tuple(_, mut elems) if elems.len() == 1 => elems.pop().unwrap(),
            x => x,
        };
        while let Some((j, Tok::Var(g))) = self.toks.next_if(|(_, t)| matches!(t, Tok::Var(_))) {
            if f != g {
                return Err((j, format!("Expected the infix function '{f}', found '{g}'")));
            }
            let y = match self.prefix("an infix argument")? {
                Ast::Tuple(_, mut elems) if elems.len() == 1 => elems.pop().unwrap(),
                y => y,
            };
            x = Ast::Infix(i, Box::new(Ast::Var(i, f)), [x.into(), y.into()], None);
        }
        Ok(x)
    }

    fn prefix(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        let mut expr = self.value(expected)?;
        while let Some((i, _)) = self.toks.next_if(|(_, t)| *t == Tok::Sep('(')) {
            let args = self.exprs("function arguments", Some(Tok::Sep(')')))?;
            expr = Ast::Prefix(i, Box::new(expr), args);
        }
        Ok(expr)
    }

    fn value(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        match self.toks.next() {
            Some((i, Tok::Sep('['))) => Ok(Ast::List(
                i,
                self.exprs("list elements after '['", Some(Tok::Sep(']')))?,
            )),
            Some((i, Tok::Sep('('))) => Ok(Ast::Tuple(
                i,
                self.exprs("tuple elements after '('", Some(Tok::Sep(')')))?,
            )),
            Some((i, Tok::Sep('{'))) => Ok(Ast::Block(
                i,
                self.exprs("block elements after '{'", Some(Tok::Sep('}')))?,
            )),
            Some((i, Tok::Var(s))) => Ok(Ast::Var(i, s)),
            Some((i, Tok::Str(s))) => Ok(Ast::String(i, s)),
            Some((i, t)) => Err((i, format!("Expected {expected}, found {t}"))),
            None => Err((self.end_pos, format!("Expected {expected}"))),
        }
    }

    fn exprs(&mut self, exp: &str, until: Option<Tok<'c>>) -> Result<Vec<Ast<'c>>, (Pos, String)> {
        let mut exprs = vec![];
        let mut last_sep = Some((self.end_pos, Tok::Sep(',')));
        loop {
            match (last_sep, self.toks.peek(), until) {
                (_, None, None) => return Ok(exprs),
                (_, Some((_, t)), Some(until)) if *t == until => {
                    self.toks.next();
                    return Ok(exprs);
                }
                (_, Some((_, Tok::Sep(',' | '\n'))), _) => last_sep = self.toks.next(),
                (_, None, Some(until)) => {
                    return Err((self.end_pos, format!("Expected {exp} to end with {until}")));
                }
                (None, Some((i, t)), None) => {
                    return Err((*i, format!("Expected ',' or '\\n', found {t}")));
                }
                (None, Some((i, t)), Some(until)) => {
                    return Err((*i, format!("Expected ',' or '\\n' or {until}, found {t}")));
                }
                (Some(_), Some(_), _) => {
                    exprs.push(self.expr(exp)?);
                    last_sep = None;
                }
            }
        }
    }
}

pub fn parse(code: &str) -> Result<Vec<Ast<'_>>, String> {
    Parser {
        end_pos: Pos(code.len()),
        toks: scan(code).into_iter().peekable(),
    }
    .exprs("an expression", None)
    .map_err(|(pos, msg)| format!("{msg} at {}", pos.line_in(code)))
}

fn fmt_ast(ast: &Ast, lvl: usize, buf: &mut String) {
    let indent = "  ";
    match ast {
        Ast::Var(_, s) => buf.push_str(s),
        Ast::String(_, s) => buf.push_str(&format!("\"{s}\"")),
        Ast::List(_, items) => {
            if items.is_empty() {
                return buf.push_str("[]");
            }
            buf.push_str("[\n");
            for (i, item) in items.iter().enumerate() {
                if i != 0 {
                    buf.push('\n');
                }
                buf.push_str(&indent.repeat(lvl + 1));
                fmt_ast(item, lvl + 1, buf);
            }
            buf.push('\n');
            buf.push_str(&indent.repeat(lvl));
            buf.push(']');
        }
        Ast::Tuple(_, items) => {
            if items.is_empty() {
                return buf.push_str("()");
            }
            buf.push_str("(\n");
            for (i, item) in items.iter().enumerate() {
                if i != 0 {
                    buf.push('\n');
                }
                buf.push_str(&indent.repeat(lvl + 1));
                fmt_ast(item, lvl + 1, buf);
            }
            buf.push('\n');
            buf.push_str(&indent.repeat(lvl));
            buf.push(')');
        }
        Ast::Block(_, items) => {
            if items.is_empty() {
                return buf.push_str("{}");
            }
            buf.push_str("{\n");
            for (i, item) in items.iter().enumerate() {
                if i != 0 {
                    buf.push('\n');
                }
                buf.push_str(&indent.repeat(lvl + 1));
                fmt_ast(item, lvl + 1, buf);
            }
            buf.push('\n');
            buf.push_str(&indent.repeat(lvl));
            buf.push('}');
        }
        Ast::Infix(_, op, [left, right], trailing) => {
            buf.push('(');
            fmt_ast(&op, lvl, buf);
            buf.push('\n');
            buf.push_str(&indent.repeat(lvl + 1));
            fmt_ast(&left, lvl + 1, buf);
            buf.push('\n');
            buf.push_str(&indent.repeat(lvl + 1));
            fmt_ast(&right, lvl + 1, buf);
            if let Some(trailing) = trailing {
                buf.push('\n');
                buf.push_str(&indent.repeat(lvl + 1));
                fmt_ast(&trailing, lvl + 1, buf);
            }
            buf.push(')');
        }
        Ast::Prefix(_, f, args) => {
            buf.push('(');
            fmt_ast(&f, lvl, buf);
            for arg in args {
                buf.push('\n');
                buf.push_str(&indent.repeat(lvl + 1));
                fmt_ast(arg, lvl + 1, buf);
            }
            buf.push(')');
        }
    }
}

impl std::fmt::Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf = String::new();
        fmt_ast(&self, 0, &mut buf);
        f.write_str(&buf)
    }
}

fn is_bare_string(s: &str) -> bool {
    s.chars().next().map_or(false, |c| c.is_ascii_uppercase()) && !s.contains(char::is_whitespace)
}

fn is_kw_list(ast: &Ast) -> bool {
    matches!(ast, Ast::List(_, items) if items.iter().all(|i| matches!(i,
        Ast::Tuple(_, elems) if matches!(elems.first(), Some(Ast::String(_, s)) if
            s.chars().next().map_or(false, |c| c.is_ascii_lowercase())))))
}

const MAX_ONE_LINE_COMPLEXITY: usize = 10;

impl Ast<'_> {
    fn size(&self) -> usize {
        match self {
            Ast::String(_, s) if s.split_whitespace().skip(1).next().is_some() => 4,
            Ast::Var(_, _) | Ast::String(_, _) => 1,
            Ast::List(_, xs) | Ast::Tuple(_, xs) | Ast::Block(_, xs) => {
                xs.iter().map(|x| x.size()).sum::<usize>() + 1
            }
            Ast::Prefix(_, f, xs) => f.size() + xs.iter().map(|x| x.size()).sum::<usize>(),
            Ast::Infix(_, _, [a, b], trailing) => {
                a.size() + 1 + b.size() + trailing.as_ref().map_or(0, |t| t.size())
            }
        }
    }

    pub fn pretty(&self) -> String {
        match self {
            Ast::Block(_, defs) => defs
                .iter()
                .map(|def| def.pretty_lvl(0))
                .collect::<Vec<_>>()
                .join("\n\n"),
            ast => ast.pretty_lvl(0),
        }
    }

    fn pretty_lvl(&self, lvl: usize) -> String {
        fn one_line(xs: &[Ast], lvl: usize) -> String {
            xs.iter()
                .map(|x| x.pretty_lvl(lvl))
                .collect::<Vec<_>>()
                .join(", ")
        }
        fn multi_line(xs: &[Ast], lvl: usize) -> String {
            let indent = "    ";
            let inner = xs
                .iter()
                .map(|x| indent.repeat(lvl) + &x.pretty_lvl(lvl) + "\n")
                .collect::<String>();
            "\n".to_string() + &inner + &indent.repeat(lvl - 1)
        }
        fn wrap(open: char, close: char, xs: &[Ast], lvl: usize, size: usize) -> String {
            if size < MAX_ONE_LINE_COMPLEXITY {
                format!("{open}{}{close}", one_line(xs, lvl + 1))
            } else {
                format!("{open}{}{close}", multi_line(xs, lvl + 1))
            }
        }
        match self {
            Ast::Var(_, s) => s.to_string(),
            Ast::String(_, s) if is_bare_string(s) => s.to_string(),
            Ast::String(_, s) => format!("\"{s}\""),
            Ast::List(_, xs) => wrap('[', ']', xs, lvl, self.size()),
            Ast::Tuple(_, xs) => {
                if let [Ast::String(_, k), v] = xs.as_slice() {
                    if k.chars().next().map_or(false, |c| c.is_ascii_lowercase()) {
                        return format!("{k}: {}", v.pretty_lvl(lvl));
                    }
                }
                wrap('(', ')', xs, lvl, self.size())
            }
            Ast::Block(_, xs) => format!("{{{}}}", multi_line(xs, lvl + 1)),
            Ast::Prefix(_, f, xs) => {
                let (args, kw) = if xs.last().map_or(false, is_kw_list) {
                    (&xs[..xs.len() - 1], Some(xs.last().unwrap()))
                } else {
                    (xs.as_slice(), None)
                };
                let split =
                    args.partition_point(|x| !matches!(x, Ast::List(_, _) | Ast::Block(_, _)));
                let call_args = &args[..split];
                let trailing_args = &args[split..];

                let size: usize = f.size() + call_args.iter().map(|x| x.size()).sum::<usize>();
                let args = if size < MAX_ONE_LINE_COMPLEXITY {
                    one_line(call_args, lvl + 1)
                } else {
                    multi_line(call_args, lvl + 1)
                };
                let has_trailing_args = !trailing_args.is_empty() || kw.is_some();
                let mut result = if call_args.is_empty() && has_trailing_args {
                    f.pretty_lvl(lvl)
                } else if trailing_args.is_empty() {
                    format!("{}({args})", f.pretty_lvl(lvl))
                } else {
                    format!("{} ({args})", f.pretty_lvl(lvl))
                };
                for t in trailing_args {
                    result.push_str(&format!(" {}", t.pretty_lvl(lvl)));
                }
                if let Some(kw_list) = kw {
                    if let Ast::List(_, kws) = kw_list {
                        for kw in kws {
                            result.push_str(&format!(" {}", kw.pretty_lvl(lvl)));
                        }
                    }
                }
                result
            }
            Ast::Infix(_, op, [a, b], trailing) => {
                let op_str = op.pretty_lvl(lvl);
                let fmt_left = |x: &Ast| match x {
                    Ast::Infix(_, inner_op, _, _) if inner_op.pretty_lvl(lvl) != op_str => {
                        format!("({})", x.pretty_lvl(lvl))
                    }
                    _ => x.pretty_lvl(lvl),
                };
                let fmt_right = |x: &Ast| match x {
                    Ast::Infix(_, _, _, _) => format!("({})", x.pretty_lvl(lvl)),
                    Ast::Tuple(_, elems) if elems.len() != 1 => x.pretty_lvl(lvl),
                    _ if trailing.is_some() => format!("({})", x.pretty_lvl(lvl)),
                    _ => x.pretty_lvl(lvl),
                };
                let base = format!("{} {} {}", fmt_left(a), op_str, fmt_right(b));
                match trailing {
                    Some(t) => format!("{base} {}", t.pretty_lvl(lvl)),
                    None => base,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example() {
        let code = include_str!("./_example.txt").trim();
        let pretty = match parse(code) {
            Ok(exprs) => exprs
                .iter()
                .map(|expr| expr.pretty())
                .collect::<Vec<_>>()
                .join("\n\n"),
            Err(e) => e,
        };
        println!("{code}\n");
        println!("{pretty}\n");
        assert_eq!(pretty, code);
    }

    fn test_many(tests: &str) -> Result<(), String> {
        let tests = tests.split("\n\n---\n\n").collect::<Vec<_>>();
        let all = tests.len();
        let mut failed = 0;
        for test in tests {
            let test = test.split("\n\n").collect::<Vec<_>>();
            let (code, expected) = (test[0], test[1]);
            let actual = match parse(code) {
                Ok(exprs) => exprs
                    .iter()
                    .map(|expr| expr.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
                Err(e) => e,
            };
            if expected.trim() != actual.trim() {
                failed += 1;
                println!("\n{code}\n");
                println!("EXPECTED:\n{expected}");
                println!("ACTUAL:\n{actual}");
            }
        }
        if failed > 0 {
            Err(format!("{failed}/{all} tests failed"))
        } else {
            Ok(())
        }
    }

    #[test]
    fn parse_ok() -> Result<(), String> {
        test_many(include_str!("./_parse_ok.txt"))
    }

    #[test]
    fn parse_err() -> Result<(), String> {
        test_many(include_str!("./_parse_err.txt"))
    }
}
