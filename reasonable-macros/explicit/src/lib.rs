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

// --- Tokens ---

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'code> {
    Sep(char),
    Var(&'code str),
    Str(&'code str),
    Bind(&'code str),
    Bind2(&'code str),
}

impl std::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tok::Sep(c) => write!(f, "'{c}'"),
            Tok::Var(s) | Tok::Str(s) => write!(f, "'{s}'"),
            Tok::Bind(s) => write!(f, "'${s}'"),
            Tok::Bind2(s) => write!(f, "'$${s}'"),
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
        if s.is_empty() {
            return;
        }
        if let Some(rest) = s.strip_prefix("$$") {
            if !rest.is_empty() {
                toks.push((Pos(i), Tok::Bind2(rest)));
            }
        } else if let Some(rest) = s.strip_prefix('$') {
            if !rest.is_empty() {
                toks.push((Pos(i), Tok::Bind(rest)));
            }
        } else if s.as_bytes()[0].is_ascii_uppercase() {
            toks.push((Pos(i), Tok::Str(s)));
        } else {
            toks.push((Pos(i), Tok::Var(s)));
        }
    }
    while let Some((j, c)) = chars.next() {
        match c {
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | '\n' => {
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

// --- Surface AST ---

#[derive(Debug, Clone)]
pub enum Ast<'code> {
    Var(Pos, &'code str),
    Str(Pos, &'code str),
    Binding(Pos, &'code str),
    DoubleBinding(Pos, &'code str),
    List(Pos, Vec<Ast<'code>>),
    Block(Pos, Vec<Ast<'code>>),
    Prefix(Pos, Box<Ast<'code>>, Vec<Ast<'code>>),
    Infix(Pos, &'code str, [Box<Ast<'code>>; 2]),
}

impl<'code> Ast<'code> {
    pub fn pos(&self) -> Pos {
        match self {
            Ast::Var(p, _)
            | Ast::Str(p, _)
            | Ast::Binding(p, _)
            | Ast::DoubleBinding(p, _)
            | Ast::List(p, _)
            | Ast::Block(p, _)
            | Ast::Prefix(p, _, _)
            | Ast::Infix(p, _, _) => *p,
        }
    }
}

impl std::fmt::Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ast::Var(_, s) | Ast::Str(_, s) => write!(f, "{s}"),
            Ast::Binding(_, s) => write!(f, "${s}"),
            Ast::DoubleBinding(_, s) => write!(f, "$${s}"),
            Ast::List(_, elems) => {
                write!(f, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "]")
            }
            Ast::Block(_, elems) if elems.is_empty() => write!(f, "{{}}"),
            Ast::Block(_, elems) => {
                write!(f, "{{ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " }}")
            }
            Ast::Prefix(_, func, args) => {
                write!(f, "{func}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Ast::Infix(_, op, [x, y]) => write!(f, "({x} {op} {y})"),
        }
    }
}

// --- Parser ---

struct Parser<'code> {
    end_pos: Pos,
    toks: std::iter::Peekable<std::vec::IntoIter<(Pos, Tok<'code>)>>,
}

impl<'c> Parser<'c> {
    fn expr(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        self.infix(expected)
    }

    fn infix(&mut self, expected: &str) -> Result<Ast<'c>, (Pos, String)> {
        let mut x = self.prefix(expected)?;
        let Some((i, Tok::Var(f))) = self.toks.peek().copied() else {
            return Ok(x);
        };
        while let Some((j, Tok::Var(g))) = self.toks.next_if(|(_, t)| matches!(t, Tok::Var(_))) {
            if f != g {
                return Err((j, format!("Expected infix '{f}', found '{g}'")));
            }
            let y = self.prefix("infix argument")?;
            x = Ast::Infix(i, f, [x.into(), y.into()]);
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
            Some((i, Tok::Sep('('))) => {
                let mut elems = self.exprs("expression after '('", Some(Tok::Sep(')')))?;
                if elems.len() == 1 {
                    Ok(elems.pop().unwrap())
                } else {
                    Ok(Ast::List(i, elems))
                }
            }
            Some((i, Tok::Sep('['))) => Ok(Ast::List(
                i,
                self.exprs("list elements", Some(Tok::Sep(']')))?,
            )),
            Some((i, Tok::Sep('{'))) => Ok(Ast::Block(
                i,
                self.exprs("block body", Some(Tok::Sep('}')))?,
            )),
            Some((i, Tok::Var(s))) => Ok(Ast::Var(i, s)),
            Some((i, Tok::Str(s))) => Ok(Ast::Str(i, s)),
            Some((i, Tok::Bind(s))) => Ok(Ast::Binding(i, s)),
            Some((i, Tok::Bind2(s))) => Ok(Ast::DoubleBinding(i, s)),
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

// --- Core AST (desugared) ---
//
// The desugared representation has no blocks or bindings. Blocks become
// sequences of calls and lambdas; bindings become plain strings.

#[derive(Debug, Clone)]
pub enum Core {
    Var(String),
    Str(String),
    List(Vec<Core>),
    Fn(String, Box<Core>),
    Call(Box<Core>, Vec<Core>),
}

impl Core {
    fn fmt_nested(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(self, Core::Fn(..)) {
            write!(f, "({self})")
        } else {
            write!(f, "{self}")
        }
    }
}

impl std::fmt::Display for Core {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Core::Var(s) => write!(f, "{s}"),
            Core::Str(s) if s.starts_with(|c: char| c.is_ascii_uppercase()) => {
                write!(f, "{s}")
            }
            Core::Str(s) => write!(f, "\"{s}\""),
            Core::List(elems) => {
                write!(f, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "]")
            }
            Core::Fn(param, body) => write!(f, "({param}) => {body}"),
            Core::Call(func, args) => {
                func.fmt_nested(f)?;
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

// --- Desugaring ---
//
// Two kinds of scope:
//
// 1. Argument scope: When a Block appears as an argument to a prefix call
//    or on the right side of an infix, it consumes all Binding/DoubleBinding
//    nodes from preceding sibling arguments and becomes a nested lambda.
//
// 2. Enclosing scope: When a block element contains bindings not consumed by
//    any inner block, those bindings are consumed by the enclosing block —
//    the rest of the block becomes a lambda passed as an extra argument.
//
// DoubleBinding contributes to BOTH scopes: it creates a lambda parameter
// in the argument-scope block AND propagates to the enclosing scope.

/// Collect bindings that propagate out of an AST node to the enclosing scope.
/// Returns (name, is_double) pairs in depth-first left-to-right order.
/// Blocks act as scope boundaries and consume preceding bindings;
/// only double bindings survive past a block boundary.
fn collect_bindings<'a>(ast: &'a Ast<'_>) -> Vec<(&'a str, bool)> {
    match ast {
        Ast::Binding(_, s) => vec![(s, false)],
        Ast::DoubleBinding(_, s) => vec![(s, true)],
        Ast::Var(..) | Ast::Str(..) | Ast::Block(..) => vec![],
        Ast::List(_, elems) => elems.iter().flat_map(collect_bindings).collect(),
        Ast::Prefix(_, f, args) => {
            let mut propagated = vec![];
            let mut pending: Vec<(&str, bool)> = collect_bindings(f);
            for arg in args {
                if matches!(arg, Ast::Block(..)) {
                    for (name, is_double) in pending.drain(..) {
                        if is_double {
                            propagated.push((name, true));
                        }
                    }
                } else {
                    pending.extend(collect_bindings(arg));
                }
            }
            propagated.extend(pending);
            propagated
        }
        Ast::Infix(_, _, [x, y]) => {
            let x_bindings = collect_bindings(x);
            if matches!(y.as_ref(), Ast::Block(..)) {
                x_bindings.into_iter().filter(|(_, d)| *d).collect()
            } else {
                let mut result = x_bindings;
                result.extend(collect_bindings(y));
                result
            }
        }
    }
}

fn has_bindings(ast: &Ast<'_>) -> bool {
    match ast {
        Ast::Binding(..) | Ast::DoubleBinding(..) => true,
        Ast::Var(..) | Ast::Str(..) | Ast::Block(..) => false,
        Ast::List(_, elems) => elems.iter().any(has_bindings),
        Ast::Prefix(_, f, args) => has_bindings(f) || args.iter().any(has_bindings),
        Ast::Infix(_, _, [x, y]) => has_bindings(x) || has_bindings(y),
    }
}

fn tag(name: &str, arg: Core) -> Core {
    Core::Call(Box::new(Core::Str(name.to_string())), vec![arg])
}

fn tag_args(name: &str, args: Vec<Core>) -> Core {
    Core::Call(Box::new(Core::Str(name.to_string())), args)
}

/// Desugar an AST node in macro-argument context, wrapping each subexpression
/// with `Binding(...)`, `Value(...)`, or `Call(...)` tags so that macro functions
/// can inspect the syntactic structure and distinguish bindings from values.
fn desugar_annotated(ast: &Ast<'_>) -> Core {
    match ast {
        Ast::Binding(_, s) | Ast::DoubleBinding(_, s) => tag("Binding", Core::Str(s.to_string())),
        Ast::Block(..) => desugar(ast),
        Ast::Var(..) | Ast::Str(..) => tag("Value", desugar(ast)),
        _ if !has_bindings(ast) => tag("Value", desugar(ast)),
        Ast::List(_, elems) => {
            let mut parts = vec![Core::Str("List".to_string())];
            parts.extend(elems.iter().map(desugar_annotated));
            tag_args("Call", parts)
        }
        Ast::Prefix(_, f, args) => {
            let mut pending: Vec<String> = vec![];
            pending.extend(collect_bindings(f).into_iter().map(|(n, _)| n.to_string()));
            let mut parts = vec![desugar_annotated(f)];
            for arg in args {
                if matches!(arg, Ast::Block(..)) {
                    let body = desugar(arg);
                    if pending.is_empty() {
                        parts.push(Core::Fn("_".to_string(), Box::new(body)));
                    } else {
                        parts.push(wrap_in_lambdas(pending.drain(..), body));
                    }
                } else {
                    pending.extend(
                        collect_bindings(arg)
                            .into_iter()
                            .map(|(n, _)| n.to_string()),
                    );
                    parts.push(desugar_annotated(arg));
                }
            }
            tag_args("Call", parts)
        }
        Ast::Infix(_, op, [x, y]) => {
            let annotated_x = desugar_annotated(x);
            let desugared_y = if matches!(y.as_ref(), Ast::Block(..)) {
                let names: Vec<String> = collect_bindings(x)
                    .into_iter()
                    .map(|(n, _)| n.to_string())
                    .collect();
                let body = desugar(y);
                if names.is_empty() {
                    Core::Fn("_".to_string(), Box::new(body))
                } else {
                    wrap_in_lambdas(names.into_iter(), body)
                }
            } else {
                desugar_annotated(y)
            };
            tag_args(
                "Call",
                vec![
                    tag("Value", Core::Var(op.to_string())),
                    annotated_x,
                    desugared_y,
                ],
            )
        }
    }
}

fn wrap_in_lambdas(names: impl DoubleEndedIterator<Item = String>, body: Core) -> Core {
    names
        .rev()
        .fold(body, |body, name| Core::Fn(name, Box::new(body)))
}

fn append_arg(expr: Core, arg: Core) -> Core {
    match expr {
        Core::Call(f, mut args) => {
            args.push(arg);
            Core::Call(f, args)
        }
        other => Core::Call(Box::new(other), vec![arg]),
    }
}

pub fn desugar(ast: &Ast<'_>) -> Core {
    match ast {
        Ast::Var(_, s) => Core::Var(s.to_string()),
        Ast::Str(_, s) => Core::Str(s.to_string()),
        Ast::Binding(_, s) | Ast::DoubleBinding(_, s) => Core::Str(s.to_string()),
        Ast::List(_, elems) => Core::List(elems.iter().map(|e| desugar(e)).collect()),
        Ast::Block(_, elems) => desugar_block(elems),
        Ast::Prefix(_, f, args) => desugar_prefix(f, args),
        Ast::Infix(_, op, [x, y]) => desugar_infix(op, x, y),
    }
}

/// Desugar a block (sequence of expressions) into Core.
///
/// Processes elements right-to-left. For each element:
/// - If it has enclosing-scope bindings: the continuation (everything after it)
///   becomes a lambda with those bindings as parameters, appended as an extra arg.
/// - If it has no bindings: the element is sequenced using `((_) => rest)(elem)`.
fn desugar_block(elems: &[Ast<'_>]) -> Core {
    if elems.is_empty() {
        return Core::Var("Unit".to_string());
    }
    let (last, init) = elems.split_last().unwrap();
    let mut result = desugar(last);
    for elem in init.iter().rev() {
        let names: Vec<String> = collect_bindings(elem)
            .into_iter()
            .map(|(name, _)| name.to_string())
            .collect();
        if names.is_empty() {
            let lambda = Core::Fn("_".to_string(), Box::new(result));
            result = Core::Call(Box::new(lambda), vec![desugar(elem)]);
        } else {
            let continuation = wrap_in_lambdas(names.into_iter(), result);
            result = append_arg(desugar(elem), continuation);
        }
    }
    result
}

/// Desugar a prefix call. Scans arguments left-to-right, accumulating binding
/// names. When a Block argument is encountered, it consumes all pending bindings
/// and becomes a nested lambda. If no bindings precede a block, it still becomes
/// a thunk `(_) => body`.
///
/// When any non-block argument contains bindings, the call is a "macro call" and
/// all non-block arguments are annotated with Value/Binding/Call wrappers.
fn desugar_prefix(f: &Ast<'_>, args: &[Ast<'_>]) -> Core {
    let mut desugared_args = vec![];
    let mut pending: Vec<String> = collect_bindings(f)
        .into_iter()
        .map(|(n, _)| n.to_string())
        .collect();
    let is_macro = has_bindings(f)
        || args
            .iter()
            .any(|a| !matches!(a, Ast::Block(..)) && has_bindings(a));

    for arg in args {
        if matches!(arg, Ast::Block(..)) {
            let body = desugar(arg);
            if pending.is_empty() {
                desugared_args.push(Core::Fn("_".to_string(), Box::new(body)));
            } else {
                desugared_args.push(wrap_in_lambdas(pending.drain(..), body));
            }
        } else {
            pending.extend(
                collect_bindings(arg)
                    .into_iter()
                    .map(|(n, _)| n.to_string()),
            );
            if is_macro {
                desugared_args.push(desugar_annotated(arg));
            } else {
                desugared_args.push(desugar(arg));
            }
        }
    }

    Core::Call(Box::new(desugar(f)), desugared_args)
}

/// Desugar an infix call. If the right side is a Block, it consumes bindings
/// from the left side and becomes a nested lambda (or thunk if no bindings).
///
/// When either operand contains bindings, the call is a "macro call" and
/// non-block operands are annotated with Value/Binding/Call wrappers.
fn desugar_infix(op: &str, x: &Ast<'_>, y: &Ast<'_>) -> Core {
    let names: Vec<String> = collect_bindings(x)
        .into_iter()
        .map(|(n, _)| n.to_string())
        .collect();

    let is_macro = has_bindings(x) || (!matches!(y, Ast::Block(..)) && has_bindings(y));

    let desugared_x = if is_macro {
        desugar_annotated(x)
    } else {
        desugar(x)
    };

    let desugared_y = if matches!(y, Ast::Block(..)) {
        let body = desugar(y);
        if names.is_empty() {
            Core::Fn("_".to_string(), Box::new(body))
        } else {
            wrap_in_lambdas(names.into_iter(), body)
        }
    } else if is_macro {
        desugar_annotated(y)
    } else {
        desugar(y)
    };

    Core::Call(
        Box::new(Core::Var(op.to_string())),
        vec![desugared_x, desugared_y],
    )
}

pub fn desugar_program(exprs: &[Ast<'_>]) -> Core {
    desugar_block(exprs)
}

pub fn parse_and_desugar(code: &str) -> Result<Core, String> {
    let ast = parse(code)?;
    Ok(desugar_program(&ast))
}

// --- Interpreter ---

type Env = Vec<(String, Value)>;

#[derive(Clone)]
pub enum Value {
    Str(String),
    Tagged(String, Vec<Value>),
    List(Vec<Value>),
    Closure(String, Core, Env),
    Builtin(&'static str, Vec<Value>),
    /// Fixed-point wrapper (Z-combinator): `Fix(f)` called with `arg` evaluates
    /// `f(Fix(f))(arg)`, giving `f` a self-reference for recursion.
    Fix(Box<Value>),
}

impl Value {
    fn is_truthy(&self) -> Result<bool, String> {
        match self {
            Value::Str(s) if s == "True" => Ok(true),
            Value::Str(s) if s == "False" => Ok(false),
            Value::Tagged(s, args) if s == "True" && args.is_empty() => Ok(true),
            Value::Tagged(s, args) if s == "False" && args.is_empty() => Ok(false),
            other => Err(format!("expected True or False, got {other}")),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Str(s) if s.starts_with(|c: char| c.is_ascii_uppercase()) => {
                write!(f, "{s}")
            }
            Value::Str(s) => write!(f, "\"{s}\""),
            Value::Tagged(tag, fields) => {
                write!(f, "{tag}")?;
                if !fields.is_empty() {
                    write!(f, "(")?;
                    for (i, v) in fields.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{v}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Value::List(elems) => {
                write!(f, "[")?;
                for (i, v) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Value::Closure(param, _, _) => write!(f, "<fn({param})>"),
            Value::Builtin(name, args) => {
                write!(f, "<builtin:{name}")?;
                if !args.is_empty() {
                    write!(f, "/{}", args.len())?;
                }
                write!(f, ">")
            }
            Value::Fix(_) => write!(f, "<rec>"),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Tagged(t1, f1), Value::Tagged(t2, f2)) => t1 == t2 && f1 == f2,
            (Value::List(a), Value::List(b)) => a == b,
            _ => false,
        }
    }
}

fn env_lookup(env: &Env, name: &str) -> Result<Value, String> {
    env.iter()
        .rev()
        .find(|(n, _)| n == name)
        .map(|(_, v)| v.clone())
        .ok_or_else(|| format!("unbound variable: {name}"))
}

const BUILTIN_NAMES: &[&str] = &[
    "=", "if", "eq", "cons", "tag", "fields", "head", "tail", "is_empty", "fix", "panic",
];

fn builtin_arity(name: &str) -> usize {
    match name {
        "=" | "if" => 3,
        "eq" | "cons" => 2,
        "tag" | "fields" | "head" | "tail" | "is_empty" | "fix" | "panic" => 1,
        _ => unreachable!(),
    }
}

fn apply_builtin(name: &str, args: &[Value]) -> Result<Value, String> {
    match (name, args) {
        ("=", [_pattern, wrapped_val, cont]) => {
            let val = match wrapped_val {
                Value::Tagged(t, fields) if t == "Value" && fields.len() == 1 => fields[0].clone(),
                Value::Closure(..) => Value::Fix(Box::new(wrapped_val.clone())),
                other => other.clone(),
            };
            apply(cont.clone(), val)
        }
        ("if", [cond, then_branch, else_branch]) => {
            let unit = Value::Str("Unit".to_string());
            if cond.is_truthy()? {
                apply(then_branch.clone(), unit)
            } else {
                apply(else_branch.clone(), unit)
            }
        }
        ("eq", [a, b]) => Ok(Value::Str(
            if a == b { "True" } else { "False" }.to_string(),
        )),
        ("tag", [val]) => match val {
            Value::Str(_) => Ok(Value::Str("Str".to_string())),
            Value::Tagged(t, _) => Ok(Value::Str(t.clone())),
            Value::List(_) => Ok(Value::Str("List".to_string())),
            Value::Closure(..) | Value::Builtin(..) | Value::Fix(..) => {
                Ok(Value::Str("Fn".to_string()))
            }
        },
        ("fields", [val]) => match val {
            Value::Tagged(_, fields) => Ok(Value::List(fields.clone())),
            other => Err(format!("fields: expected tagged value, got {other}")),
        },
        ("head", [val]) => match val {
            Value::List(elems) if !elems.is_empty() => Ok(elems[0].clone()),
            Value::List(_) => Err("head: empty list".to_string()),
            other => Err(format!("head: expected list, got {other}")),
        },
        ("tail", [val]) => match val {
            Value::List(elems) if !elems.is_empty() => Ok(Value::List(elems[1..].to_vec())),
            Value::List(_) => Err("tail: empty list".to_string()),
            other => Err(format!("tail: expected list, got {other}")),
        },
        ("is_empty", [val]) => match val {
            Value::List(elems) => Ok(Value::Str(
                if elems.is_empty() { "True" } else { "False" }.to_string(),
            )),
            other => Err(format!("is_empty: expected list, got {other}")),
        },
        ("fix", [f]) => Ok(Value::Fix(Box::new(f.clone()))),
        ("cons", [elem, list]) => match list {
            Value::List(elems) => {
                let mut new = vec![elem.clone()];
                new.extend(elems.iter().cloned());
                Ok(Value::List(new))
            }
            other => Err(format!("cons: expected list, got {other}")),
        },
        ("panic", [val]) => Err(format!("panic: {val}")),
        _ => Err(format!("builtin {name}: wrong number of arguments")),
    }
}

fn apply(func: Value, arg: Value) -> Result<Value, String> {
    match func {
        Value::Closure(param, body, mut env) => {
            env.push((param, arg));
            eval(&body, &env)
        }
        Value::Fix(f) => {
            let self_ref = Value::Fix(f.clone());
            let inner = apply(*f, self_ref)?;
            apply(inner, arg)
        }
        Value::Str(tag) => Ok(Value::Tagged(tag, vec![arg])),
        Value::Tagged(tag, mut fields) => {
            fields.push(arg);
            Ok(Value::Tagged(tag, fields))
        }
        Value::Builtin(name, mut partial) => {
            partial.push(arg);
            if partial.len() == builtin_arity(name) {
                apply_builtin(name, &partial)
            } else {
                Ok(Value::Builtin(name, partial))
            }
        }
        other => Err(format!("cannot call {other}")),
    }
}

pub fn eval(expr: &Core, env: &Env) -> Result<Value, String> {
    match expr {
        Core::Var(name) => env_lookup(env, name),
        Core::Str(s) => Ok(Value::Str(s.clone())),
        Core::List(elems) => {
            let values: Result<Vec<_>, _> = elems.iter().map(|e| eval(e, env)).collect();
            Ok(Value::List(values?))
        }
        Core::Fn(param, body) => Ok(Value::Closure(param.clone(), *body.clone(), env.clone())),
        Core::Call(func_expr, arg_exprs) => {
            let mut result = eval(func_expr, env)?;
            for arg_expr in arg_exprs {
                let arg = eval(arg_expr, env)?;
                result = apply(result, arg)?;
            }
            Ok(result)
        }
    }
}

fn default_env() -> Env {
    let mut env = Env::new();
    for &name in BUILTIN_NAMES {
        env.push((name.to_string(), Value::Builtin(name, vec![])));
    }
    env.push(("True".to_string(), Value::Str("True".to_string())));
    env.push(("False".to_string(), Value::Str("False".to_string())));
    env.push(("Unit".to_string(), Value::Str("Unit".to_string())));
    env.push(("=>".to_string(), Value::Str("=>".to_string())));
    env
}

/// Pattern matching library, loaded as a prelude before user code.
///
/// Provides `match(value, [pattern => { body }, ...])` where patterns can be
/// bindings (`$x`), literal values, or constructor patterns (`Tag($x, $y)`).
/// Supports unification: repeated bindings (`$x, $x`) require equal values.
const PRELUDE: &str = r#"
$$lookup($name, $list) = {
  if(is_empty(list), { NotFound }, {
    $entry = head(list)
    if(eq(name, head(fields(entry))),
      { Found(head(tail(fields(entry)))) },
      { lookup(name, tail(list)) })
  })
}
$$match_pat($v, $pat, $body, $seen) = {
  if(eq(tag(pat), Binding), {
    $name = head(fields(pat))
    $prev = lookup(name, seen)
    if(eq(tag(prev), Found), {
      if(eq(v, head(fields(prev))),
        { Ok(body(v), seen) },
        { Fail })
    }, {
      Ok(body(v), cons(Pair(name, v), seen))
    })
  }, {
    if(eq(tag(pat), Value), {
      if(eq(v, head(fields(pat))),
        { Ok(body, seen) },
        { Fail })
    }, {
      $constructor = head(fields(pat))
      $expected_tag = if(eq(tag(constructor), Value),
        { head(fields(constructor)) }, { constructor })
      if(eq(tag(v), expected_tag), {
        $$go($vals, $pats, $b, $s) = {
          if(is_empty(pats), { Ok(b, s) }, {
            $result = match_pat(head(vals), head(pats), b, s)
            if(eq(tag(result), Ok), {
              go(tail(vals), tail(pats), head(fields(result)), head(tail(fields(result))))
            }, { Fail })
          })
        }
        go(fields(v), tail(fields(pat)), body, seen)
      }, { Fail })
    })
  })
}
$$try_arm($v, $arm) = {
  if(eq(tag(arm), Call), {
    $parts = tail(fields(arm))
    match_pat(v, head(parts), head(tail(parts)), [])
  }, {
    $inner = head(fields(arm))
    $lit = head(fields(inner))
    $thunk = head(tail(fields(inner)))
    if(eq(v, lit), { Ok(thunk(Unit), []) }, { Fail })
  })
}
$$try_arms($v, $arms) = {
  if(is_empty(arms), { panic(NoMatch) }, {
    $result = try_arm(v, head(arms))
    if(eq(tag(result), Ok), {
      head(fields(result))
    }, {
      try_arms(v, tail(arms))
    })
  })
}
$$match($value, $arms) = {
  $v = head(fields(value))
  $arm_list = tail(fields(arms))
  try_arms(v, arm_list)
}
"#;

pub fn run(code: &str) -> Result<Value, String> {
    let full_code = format!("{{ {PRELUDE} {code} }}");
    let core = parse_and_desugar(&full_code)?;
    eval(&core, &default_env())
}

// --- Tests ---

#[cfg(test)]
mod tests {
    use super::*;

    // -- Parser tests --

    fn p(code: &str) -> String {
        parse(code)
            .map(|exprs| {
                exprs
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join("; ")
            })
            .unwrap_or_else(|e| format!("ERROR: {e}"))
    }

    #[test]
    fn atoms() {
        assert_eq!(p("x"), "x");
        assert_eq!(p("Foo"), "Foo");
        assert_eq!(p("\"hello\""), "hello");
        assert_eq!(p("$x"), "$x");
        assert_eq!(p("$$x"), "$$x");
    }

    #[test]
    fn prefix_calls() {
        assert_eq!(p("f(x)"), "f(x)");
        assert_eq!(p("f(x, y)"), "f(x, y)");
        assert_eq!(p("f(x)(y)"), "f(x)(y)");
        assert_eq!(p("Pair($x, $y)"), "Pair($x, $y)");
    }

    #[test]
    fn infix_calls() {
        assert_eq!(p("a + b"), "(a + b)");
        assert_eq!(p("a + b + c"), "((a + b) + c)");
        assert_eq!(p("$x = Foo"), "($x = Foo)");
    }

    #[test]
    fn infix_in_args() {
        assert_eq!(p("f(a + b)"), "f((a + b))");
        assert_eq!(p("f((a + b))"), "f((a + b))");
    }

    #[test]
    fn blocks() {
        assert_eq!(p("{ x }"), "{ x }");
        assert_eq!(p("{ f(x), g(y) }"), "{ f(x); g(y) }");
        assert_eq!(p("{}"), "{}");
    }

    #[test]
    fn lists() {
        assert_eq!(p("[x, y, z]"), "[x, y, z]");
        assert_eq!(p("[]"), "[]");
    }

    #[test]
    fn grouping() {
        assert_eq!(p("(x)"), "x");
        assert_eq!(p("f((a + b))"), "f((a + b))");
        assert_eq!(p("(x, y)"), "[x, y]");
    }

    #[test]
    fn pattern_arrow() {
        assert_eq!(p("Pair($x, $x) => { x }"), "(Pair($x, $x) => { x })");
    }

    #[test]
    fn enclosing_scope() {
        assert_eq!(p("{ $x = \"hello\", f(x) }"), "{ ($x = hello); f(x) }");
    }

    #[test]
    fn full_match() {
        assert_eq!(
            p("match(v, [Pair($x, $x) => { x }])"),
            "match(v, [(Pair($x, $x) => { x })])"
        );
    }

    #[test]
    fn recursive_fn() {
        assert_eq!(
            p("{ $$f($x, $y) = { f(x, y) }, f(Foo, Bar) }"),
            "{ ($$f($x, $y) = { f(x, y) }); f(Foo, Bar) }"
        );
    }

    #[test]
    fn comments() {
        assert_eq!(p("x // comment\ny"), "x; y");
    }

    #[test]
    fn multiline() {
        assert_eq!(p("a\nb\nc"), "a; b; c");
    }

    #[test]
    fn nested_blocks() {
        assert_eq!(
            p("{ $x = Foo, { $y = Bar, f(x, y) } }"),
            "{ ($x = Foo); { ($y = Bar); f(x, y) } }"
        );
    }

    #[test]
    fn lambda_syntax() {
        assert_eq!(p("($x, $y) => { x + y }"), "([$x, $y] => { (x + y) })");
    }

    #[test]
    fn match_with_multiple_arms() {
        let code = "match(v, [\n  Pair($x, $x) => { x }\n  $y => { y }\n])";
        assert_eq!(
            p(code),
            "match(v, [(Pair($x, $x) => { x }), ($y => { y })])"
        );
    }

    // -- Desugaring tests --

    fn d(code: &str) -> String {
        parse_and_desugar(code).unwrap().to_string()
    }

    #[test]
    fn desugar_var() {
        assert_eq!(d("x"), "x");
    }

    #[test]
    fn desugar_tag() {
        assert_eq!(d("Foo"), "Foo");
    }

    #[test]
    fn desugar_binding_becomes_str() {
        assert_eq!(d("$x"), "\"x\"");
        assert_eq!(d("$$y"), "\"y\"");
    }

    #[test]
    fn desugar_prefix_no_bindings() {
        assert_eq!(d("f(x, y)"), "f(x, y)");
    }

    #[test]
    fn desugar_infix_no_bindings() {
        assert_eq!(d("a + b"), "+(a, b)");
    }

    #[test]
    fn desugar_sequencing() {
        assert_eq!(d("{ f(x), g(y) }"), "((_) => g(y))(f(x))");
    }

    #[test]
    fn desugar_three_element_sequence() {
        assert_eq!(d("{ a, b, c }"), "((_) => ((_) => c)(b))(a)");
    }

    #[test]
    fn desugar_enclosing_scope_binding() {
        assert_eq!(
            d("{ $x = \"hello\", f(x) }"),
            "=(Binding(\"x\"), Value(\"hello\"), (x) => f(x))"
        );
    }

    #[test]
    fn desugar_nested_enclosing() {
        assert_eq!(
            d("{ $a = x, $b = y, Pair(a, b) }"),
            "=(Binding(\"a\"), Value(x), (a) => =(Binding(\"b\"), Value(y), (b) => Pair(a, b)))"
        );
    }

    #[test]
    fn desugar_argument_scope_infix() {
        assert_eq!(
            d("Pair($x, $x) => { x }"),
            "=>(Call(Value(Pair), Binding(\"x\"), Binding(\"x\")), (x) => (x) => x)"
        );
    }

    #[test]
    fn desugar_argument_scope_prefix() {
        assert_eq!(
            d("match(v, Pair($x, $x), { x })"),
            "match(Value(v), Call(Value(Pair), Binding(\"x\"), Binding(\"x\")), (x) => (x) => x)"
        );
    }

    #[test]
    fn desugar_block_arg_no_bindings() {
        assert_eq!(d("f({ x })"), "f((_) => x)");
    }

    #[test]
    fn desugar_full_match() {
        assert_eq!(
            d("match(v, [Pair($x, $x) => { x }])"),
            "match(Value(v), Call(List, Call(Value(=>), Call(Value(Pair), Binding(\"x\"), Binding(\"x\")), (x) => (x) => x)))"
        );
    }

    #[test]
    fn desugar_match_multiple_arms() {
        assert_eq!(
            d("match(v, [\n  Pair($x, $x) => { x }\n  $y => { y }\n])"),
            "match(Value(v), Call(List, Call(Value(=>), Call(Value(Pair), Binding(\"x\"), Binding(\"x\")), (x) => (x) => x), Call(Value(=>), Binding(\"y\"), (y) => y)))"
        );
    }

    #[test]
    fn desugar_double_binding() {
        assert_eq!(
            d("{ $$f($x, $y) = { f(x, y) }, f(Foo, Bar) }"),
            "=(Call(Binding(\"f\"), Binding(\"x\"), Binding(\"y\")), (f) => (x) => (y) => f(x, y), (f) => f(Foo, Bar))"
        );
    }

    #[test]
    fn desugar_nested_blocks() {
        assert_eq!(
            d("{ $x = Foo, { $y = Bar, f(x, y) } }"),
            "=(Binding(\"x\"), Value(Foo), (x) => =(Binding(\"y\"), Value(Bar), (y) => f(x, y)))"
        );
    }

    #[test]
    fn desugar_lambda_syntax() {
        assert_eq!(
            d("($x, $y) => { x + y }"),
            "=>(Call(List, Binding(\"x\"), Binding(\"y\")), (x) => (y) => +(x, y))"
        );
    }

    #[test]
    fn desugar_inner_block_consumed() {
        assert_eq!(
            d("f(g($x, { x }), { y })"),
            "f(Call(Value(g), Binding(\"x\"), (x) => x), (_) => y)"
        );
    }

    #[test]
    fn desugar_chained_prefix() {
        assert_eq!(d("f(x)(y)"), "f(x)(y)");
    }

    #[test]
    fn desugar_empty_block() {
        assert_eq!(d("{}"), "Unit");
    }

    #[test]
    fn desugar_mixed_binding_and_sequence() {
        assert_eq!(
            d("{ $x = Foo, print(x), f(x) }"),
            "=(Binding(\"x\"), Value(Foo), (x) => ((_) => f(x))(print(x)))"
        );
    }

    #[test]
    fn desugar_annotation_distinguishes_bindings() {
        // These three cases must produce distinct desugared output
        let a = d("Pair($x, \"y\") => { x }");
        let b = d("$Pair($x, \"y\") => { x }");
        let c = d("$Pair($x, $y) => { x }");
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_eq!(
            a,
            "=>(Call(Value(Pair), Binding(\"x\"), Value(\"y\")), (x) => x)"
        );
        assert_eq!(
            b,
            "=>(Call(Binding(Pair), Binding(\"x\"), Value(\"y\")), (Pair) => (x) => x)"
        );
        assert_eq!(
            c,
            "=>(Call(Binding(Pair), Binding(\"x\"), Binding(\"y\")), (Pair) => (x) => (y) => x)"
        );
    }

    // -- Interpreter tests --

    fn r(code: &str) -> String {
        run(code)
            .map(|v| v.to_string())
            .unwrap_or_else(|e| format!("ERROR: {e}"))
    }

    #[test]
    fn eval_str() {
        assert_eq!(r("\"hello\""), "\"hello\"");
    }

    #[test]
    fn eval_tag_atom() {
        assert_eq!(r("True"), "True");
        assert_eq!(r("Foo"), "Foo");
    }

    #[test]
    fn eval_tagged_value() {
        assert_eq!(r("Pair(True, False)"), "Pair(True, False)");
        assert_eq!(r("Just(\"hello\")"), "Just(\"hello\")");
    }

    #[test]
    fn eval_nested_tagged() {
        assert_eq!(r("Pair(Just(True), Nothing)"), "Pair(Just(True), Nothing)");
    }

    #[test]
    fn eval_list() {
        assert_eq!(r("[True, False, Unit]"), "[True, False, Unit]");
        assert_eq!(r("[]"), "[]");
    }

    #[test]
    fn eval_if_true() {
        assert_eq!(r("if(True, { Foo }, { Bar })"), "Foo");
    }

    #[test]
    fn eval_if_false() {
        assert_eq!(r("if(False, { Foo }, { Bar })"), "Bar");
    }

    #[test]
    fn eval_if_nested() {
        assert_eq!(
            r("if(False, { Foo }, { if(True, { Bar }, { Baz }) })"),
            "Bar"
        );
    }

    #[test]
    fn eval_eq_strings() {
        assert_eq!(r("eq(\"hello\", \"hello\")"), "True");
        assert_eq!(r("eq(\"hello\", \"world\")"), "False");
    }

    #[test]
    fn eval_eq_tags() {
        assert_eq!(r("eq(Pair(True, False), Pair(True, False))"), "True");
        assert_eq!(r("eq(Pair(True, False), Pair(True, True))"), "False");
        assert_eq!(r("eq(Foo, Bar)"), "False");
    }

    #[test]
    fn eval_tag_builtin() {
        assert_eq!(r("tag(Pair(True, False))"), "Pair");
        assert_eq!(r("tag(\"hello\")"), "Str");
        assert_eq!(r("tag([True])"), "List");
        assert_eq!(r("tag(True)"), "Str");
    }

    #[test]
    fn eval_fields() {
        assert_eq!(r("fields(Pair(True, False))"), "[True, False]");
        assert_eq!(r("fields(Just(Foo))"), "[Foo]");
    }

    #[test]
    fn eval_head() {
        assert_eq!(r("head([Foo, Bar, Baz])"), "Foo");
    }

    #[test]
    fn eval_tail() {
        assert_eq!(r("tail([Foo, Bar, Baz])"), "[Bar, Baz]");
        assert_eq!(r("tail([Foo])"), "[]");
    }

    #[test]
    fn eval_is_empty() {
        assert_eq!(r("is_empty([])"), "True");
        assert_eq!(r("is_empty([Foo])"), "False");
    }

    #[test]
    fn eval_panic() {
        assert_eq!(r("panic(\"oops\")"), "ERROR: panic: \"oops\"");
    }

    #[test]
    fn eval_sequencing() {
        assert_eq!(r("{ True, False, Foo }"), "Foo");
    }

    #[test]
    fn eval_simple_binding() {
        assert_eq!(r("{ $x = Foo, x }"), "Foo");
    }

    #[test]
    fn eval_nested_binding() {
        assert_eq!(
            r("{ $x = Foo, { $y = Bar, Pair(x, y) } }"),
            "Pair(Foo, Bar)"
        );
    }

    #[test]
    fn eval_binding_with_complex_value() {
        assert_eq!(r("{ $v = Pair(Foo, Bar), tag(v) }"), "Pair");
    }

    #[test]
    fn eval_partial_builtin() {
        assert_eq!(r("{ $eq_foo = eq(Foo), eq_foo(Foo) }"), "True");
        assert_eq!(r("{ $eq_foo = eq(Foo), eq_foo(Bar) }"), "False");
    }

    #[test]
    fn eval_tag_check_and_branch() {
        assert_eq!(
            r(
                "{ $v = Pair(Foo, Bar), if(eq(tag(v), \"Pair\"), { head(fields(v)) }, { Nothing }) }"
            ),
            "Foo"
        );
    }

    #[test]
    fn eval_tag_check_mismatch() {
        assert_eq!(
            r("{ $v = Just(Foo), if(eq(tag(v), \"Pair\"), { head(fields(v)) }, { Nothing }) }"),
            "Nothing"
        );
    }

    #[test]
    fn eval_head_tail_traversal() {
        assert_eq!(
            r("{ $v = Triple(Foo, Bar, Baz), head(tail(tail(fields(v)))) }"),
            "Baz"
        );
    }

    #[test]
    fn eval_list_operations_chain() {
        assert_eq!(
            r("{ $list = [Foo, Bar, Baz], if(is_empty(list), { Nothing }, { head(list) }) }"),
            "Foo"
        );
    }

    #[test]
    fn eval_block_as_thunk() {
        assert_eq!(
            r("{ $apply_thunk = if(True, { Pair(Foo, Bar) }, { Nothing }), apply_thunk }"),
            "Pair(Foo, Bar)"
        );
    }

    #[test]
    fn eval_cons() {
        assert_eq!(r("cons(Foo, [Bar, Baz])"), "[Foo, Bar, Baz]");
        assert_eq!(r("cons(Foo, [])"), "[Foo]");
    }

    #[test]
    fn eval_recursive_length() {
        assert_eq!(
            r(
                "{ $$len($list) = { if(is_empty(list), { Zero }, { Succ(len(tail(list))) }) }, len([A, B, C]) }"
            ),
            "Succ(Succ(Succ(Zero)))"
        );
    }

    #[test]
    fn eval_recursive_countdown() {
        assert_eq!(
            r(
                "{ $$go($list) = { if(is_empty(list), { Done }, { go(tail(list)) }) }, go([A, B, C]) }"
            ),
            "Done"
        );
    }

    #[test]
    fn eval_map() {
        assert_eq!(
            r("{
                $$map($f, $list) = {
                    if(is_empty(list), { [] }, { cons(f(head(list)), map(f, tail(list))) })
                }
                map(Just, [Foo, Bar, Baz])
            }"),
            "[Just(Foo), Just(Bar), Just(Baz)]"
        );
    }

    #[test]
    fn eval_fold() {
        assert_eq!(
            r("{
                $$fold($f, $acc, $list) = {
                    if(is_empty(list), { acc }, { fold(f, f(acc, head(list)), tail(list)) })
                }
                fold(Pair, Nil, [Foo, Bar, Baz])
            }"),
            "Pair(Pair(Pair(Nil, Foo), Bar), Baz)"
        );
    }

    #[test]
    fn eval_reverse() {
        assert_eq!(
            r("{
                $$fold($f, $acc, $list) = {
                    if(is_empty(list), { acc }, { fold(f, f(acc, head(list)), tail(list)) })
                }
                $$flip_cons($acc, $x) = { cons(x, acc) }
                $$reverse($list) = { fold(flip_cons, [], list) }
                reverse([Foo, Bar, Baz])
            }"),
            "[Baz, Bar, Foo]"
        );
    }

    #[test]
    fn eval_map_over_empty() {
        assert_eq!(
            r("{
                $$map($f, $list) = {
                    if(is_empty(list), { [] }, { cons(f(head(list)), map(f, tail(list))) })
                }
                map(Just, [])
            }"),
            "[]"
        );
    }

    // -- Pattern matching tests --

    #[test]
    fn eval_match_basic_destructuring() {
        assert_eq!(
            r("match(Pair(Foo, Bar), [Pair($x, $y) => { Pair(y, x) }])"),
            "Pair(Bar, Foo)"
        );
    }

    #[test]
    fn eval_match_wildcard() {
        assert_eq!(r("match(Hello, [$x => { x }])"), "Hello");
    }

    #[test]
    fn eval_match_unification_success() {
        assert_eq!(r("match(Pair(Foo, Foo), [Pair($x, $x) => { x }])"), "Foo");
    }

    #[test]
    fn eval_match_unification_failure_fallthrough() {
        assert_eq!(
            r("match(Pair(Foo, Bar), [
                Pair($x, $x) => { Unified(x) }
                Pair($a, $b) => { Distinct(a, b) }
            ])"),
            "Distinct(Foo, Bar)"
        );
    }

    #[test]
    fn eval_match_value_binding() {
        assert_eq!(
            r("{
                $y = Bar
                match(Pair(Foo, Bar), [Pair($x, y) => { x }])
            }"),
            "Foo"
        );
    }

    #[test]
    fn eval_match_value_mismatch_fallthrough() {
        assert_eq!(
            r("{
                $y = Baz
                match(Pair(Foo, Bar), [
                    Pair($x, y) => { FoundIt(x) }
                    $z => { Fallback(z) }
                ])
            }"),
            "Fallback(Pair(Foo, Bar))"
        );
    }

    #[test]
    fn eval_match_nested_pattern() {
        assert_eq!(
            r("match(Just(Pair(Foo, Bar)), [
                Just(Pair($x, $y)) => { Pair(y, x) }
            ])"),
            "Pair(Bar, Foo)"
        );
    }

    #[test]
    fn eval_match_tag_mismatch() {
        assert_eq!(
            r("match(Left(Foo), [
                Right($x) => { GotRight(x) }
                Left($x) => { GotLeft(x) }
            ])"),
            "GotLeft(Foo)"
        );
    }

    #[test]
    fn eval_match_literal_arm() {
        assert_eq!(
            r("match(False, [
                True => { Yes }
                $other => { No(other) }
            ])"),
            "No(False)"
        );
    }

    #[test]
    fn eval_match_multiple_fields() {
        assert_eq!(
            r("match(Triple(A, B, C), [
                Triple($x, $y, $z) => { Result(z, y, x) }
            ])"),
            "Result(C, B, A)"
        );
    }
}
