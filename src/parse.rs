use expr::{Expr, Term, Type};

use std::error;
use std::fmt;
use std::io;
use std::io::{Bytes, Read};
use std::mem;
use std::ops::Deref;

enum Parse<T> {
    Parsed(T),
    Other(Located<Token>),
    EOF(Position),
}

impl<T> Parse<T> {
    fn ok_or(self, s: &str) -> Result<T, LocatedError> {
        use self::Parse::*;
        match self {
            Parsed(t) => Ok(t),
            Other(Located(p, t)) => Err(Located(p, Error::expect(s, t))),
            EOF(p) => Err(Located(p, Error::EOF(s.to_string()))),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Located<T>(Position, T);

pub type LocatedError = Located<Error>;

impl<T> Deref for Located<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.1
    }
}

impl fmt::Display for LocatedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: ", self.0)?;
        self.1.fmt(f)
    }
}

impl error::Error for LocatedError {
    fn description(&self) -> &str {
        self.1.description()
    }
}

impl From<LocatedError> for Error {
    fn from(e: LocatedError) -> Error {
        e.1
    }
}

#[derive(Debug)]
pub enum Error {
    EOF(String),
    Io(io::Error),
    Expect(String, Token),
    Trailing(Token),
    Illegal(u8),
}

pub fn parse<R>(r: R) -> Result<Expr, LocatedError>
where
    R: Read,
{
    let mut p = Parser::new(r)?;
    let e = p.parse()?.ok_or("expression")?;
    if let Some(t) = p.take() {
        Err(Located(t.0, Error::Trailing(t.1)))
    } else {
        Ok(e)
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Position(usize, usize);

struct Lexer<R> {
    b: Bytes<R>,
    current: u8,
    eof: bool,
    line: usize,
    column: usize,
}

struct Parser<R> {
    lexer: Lexer<R>,
    current: Option<Located<Token>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Number(usize),
    Ident(String),
    Int,
    Lambda,
    RArrow,
    Colon,
    Dot,
    BinOp(BinOpKind),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinOpKind {
    Plus,
    Minus,
}

fn is_whitespace(b: u8) -> bool {
    match b {
        b' ' | b'\n' => true,
        _ => false,
    }
}

fn is_digit(b: u8) -> bool {
    match b {
        b'0'...b'9' => true,
        _ => false,
    }
}

fn is_digit_start(b: u8) -> bool {
    match b {
        b'1'...b'9' => true,
        _ => false,
    }
}

fn is_ident_start(b: u8) -> bool {
    match b {
        b'a'...b'z' | b'A'...b'Z' => true,
        _ => false,
    }
}

fn is_ident(b: u8) -> bool {
    match b {
        _ if is_ident_start(b) || is_digit(b) => true,
        _ => false,
    }
}

impl<R: Read> Lexer<R> {
    fn new(mut b: Bytes<R>) -> Result<Lexer<R>, LocatedError> {
        let mut eof = false;
        let mut current = 0;
        match b.next() {
            None => eof = true,
            Some(Err(e)) => {
                return Err(Located(Position(1, 1), Error::from(e)));
            }
            Some(Ok(u)) => {
                current = u;
            }
        }
        Ok(Lexer {
            b,
            current,
            eof,
            line: 0,
            column: 0,
        })
    }

    fn from_read(r: R) -> Result<Lexer<R>, LocatedError> {
        Lexer::new(r.bytes())
    }

    /// Return the position. Its line and column are start from 1.
    fn position(&self) -> Position {
        Position(self.line + 1, self.column + 1)
    }

    fn next_store(&mut self) -> Result<(), LocatedError> {
        if let Some(r) = self.next() {
            self.current = r?;
        } else {
            self.eof = true;
        }
        Ok(())
    }

    fn next(&mut self) -> Option<Result<u8, LocatedError>> {
        let ret = self.b
            .next()?
            .map_err(|e| Located(self.position(), Error::Io(e)));
        if let Ok(b) = ret {
            if b == b'\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
        }
        Some(ret)
    }

    fn lex(&mut self) -> Result<Option<Located<Token>>, LocatedError> {
        use self::Token::*;
        self.skip_whitespace()?;
        if self.eof {
            return Ok(None);
        }
        let p = self.position();
        macro_rules! ret {
            ($x:expr) => {
                $x.map(|o| o.map(|t| Located(p, t)))
            }
        }
        match self.current {
            b if is_digit_start(b) => ret!(self.lex_number()),
            b if is_ident_start(b) => ret!(self.lex_ident()),
            b'\\' => ret!(self.proceed(Lambda)),
            b'-' => ret!(self.lex_hyphen()),
            b':' => ret!(self.proceed(Colon)),
            b'.' => ret!(self.proceed(Dot)),
            b'+' => ret!(self.proceed(BinOp(BinOpKind::Plus))),
            b => Err(Located(p, Error::Illegal(b))),
        }
    }

    fn lex_number(&mut self) -> Result<Option<Token>, LocatedError> {
        let f = |buf: &Lexer<_>| (buf.current - b'0') as usize;
        let mut n = f(self);
        loop {
            self.next_store()?;
            if self.eof || !is_digit(self.current) {
                return Ok(Some(Token::Number(n)));
            }
            n = n * 10 + f(self)
        }
    }

    fn lex_ident(&mut self) -> Result<Option<Token>, LocatedError> {
        let mut vec = vec![];
        vec.push(self.current);
        loop {
            self.next_store()?;
            if self.eof || !is_ident(self.current) {
                let s = unsafe { String::from_utf8_unchecked(vec) };
                return Ok(Some(if s == "int" {
                    Token::Int
                } else {
                    Token::Ident(s)
                }));
            }
            vec.push(self.current);
        }
    }

    fn proceed(&mut self, t: Token) -> Result<Option<Token>, LocatedError> {
        self.next_store()?;
        Ok(Some(t))
    }

    fn lex_hyphen(&mut self) -> Result<Option<Token>, LocatedError> {
        self.next_store()?;
        Ok(Some(if self.eof || self.current != b'>' {
            Token::BinOp(BinOpKind::Minus)
        } else {
            self.next_store()?;
            Token::RArrow
        }))
    }

    fn skip_whitespace(&mut self) -> Result<(), LocatedError> {
        while !self.eof && is_whitespace(self.current) {
            self.next_store()?;
        }
        Ok(())
    }
}

impl<R: Read> Parser<R> {
    fn new(r: R) -> Result<Parser<R>, LocatedError> {
        let l = Lexer::from_read(r)?;
        Parser::from_lexer(l)
    }

    fn from_lexer(mut lexer: Lexer<R>) -> Result<Parser<R>, LocatedError> {
        let t = lexer.lex()?;
        Ok(Parser { lexer, current: t })
    }

    fn position(&self) -> Position {
        self.lexer.position()
    }

    fn lex(&mut self) -> Result<(), LocatedError> {
        self.current = self.lexer.lex()?;
        Ok(())
    }

    fn next(&mut self) -> Result<Option<Located<Token>>, LocatedError> {
        self.lexer.lex().map(|t| mem::replace(&mut self.current, t))
    }

    fn take(&mut self) -> Option<Located<Token>> {
        mem::replace(&mut self.current, None)
    }

    fn current_or_eof(&self, s: &str) -> Result<&Located<Token>, LocatedError> {
        let t = self.current.as_ref();
        t.ok_or(Located(self.position(), Error::EOF(s.to_string())))
    }

    fn parse(&mut self) -> Result<Parse<Expr>, LocatedError> {
        match self.current_or_eof("expression")?.1 {
            Token::Lambda => {
                self.lex()?;
                self.parse_abs().map(|x| Parse::Parsed(x))
            }
            _ => self.parse_expr(),
        }
    }

    fn parse_expr(&mut self) -> Result<Parse<Expr>, LocatedError> {
        use self::Parse::*;
        let mut e0: Expr;
        match self.parse_term()? {
            Parsed(e) => e0 = e,
            p => return Ok(p),
        }
        loop {
            let k0: BinOpKind;
            match self.parse_binary_operator()? {
                Parsed(k) => k0 = k,
                _ => return Ok(Parsed(e0)),
            }
            let e1 = self.parse_term()?.ok_or("term")?;
            match k0 {
                BinOpKind::Plus => e0 = Expr::add(e0, e1),
                BinOpKind::Minus => e0 = Expr::sub(e0, e1),
            }
        }
    }

    fn proceed<T>(&mut self, x: T) -> Result<Parse<T>, LocatedError> {
        self.lex()?;
        Ok(Parse::Parsed(x))
    }

    fn parse_binary_operator(&mut self) -> Result<Parse<BinOpKind>, LocatedError> {
        use self::Token::*;
        Ok(match self.current {
            Some(Located(_, BinOp(k))) => self.proceed(k)?,
            Some(ref t) => Parse::Other(t.clone()),
            None => Parse::EOF(self.position()),
        })
    }

    fn parse_term(&mut self) -> Result<Parse<Expr>, LocatedError> {
        use self::Parse::*;
        let e0: Expr;
        match self.parse_factor()? {
            Parsed(e) => e0 = e,
            p => return Ok(p),
        }
        let mut v = vec![];
        loop {
            match self.parse_factor()? {
                Parsed(e1) => v.push(e1),
                _ => {
                    return Ok(Parsed(
                        v.into_iter().fold(e0, |e, e1| Expr::Term(Term::app(e, e1))),
                    ))
                }
            }
        }
    }

    fn parse_factor(&mut self) -> Result<Parse<Expr>, LocatedError> {
        Ok(match self.take() {
            Some(Located(_, Token::Number(n))) => self.proceed(Expr::Term(Term::Int(n as isize)))?,
            Some(Located(_, Token::Ident(s))) => self.proceed(Expr::Term(Term::Var(s)))?,
            Some(t) => {
                mem::swap(&mut self.current, &mut Some(t.clone()));
                Parse::Other(t)
            }
            None => Parse::EOF(self.position()),
        })
    }

    fn parse_abs(&mut self) -> Result<Expr, LocatedError> {
        macro_rules! expect {
            ($t:expr, $p:pat, $body:expr) => {
                match self.next()?.ok_or(Located(self.position(), Error::EOF($t.to_string())))? {
                    Located(_, $p) => $body,
                    Located(p, t) => return Err(Located(p, Error::expect($t, t))),
                }
            }
        }
        expect!(
            "ident",
            Token::Ident(s),
            expect!("colon", Token::Colon, {
                let ty = self.parse_type()?;
                expect!("dot", Token::Dot, {
                    let body = self.parse()?.ok_or("expression")?;
                    return Ok(Expr::Term(Term::Abs(s, ty, Box::new(body))));
                })
            })
        );
    }

    fn parse_type(&mut self) -> Result<Type, LocatedError> {
        let a = self.parse_atomic_type()?;
        {
            if self.current.as_ref().map_or(true, |l| !l.is_right_arrow()) {
                return Ok(a);
            }
        }
        self.lex()?;
        Ok(Type::arr(a, self.parse_type()?))
    }

    fn parse_atomic_type(&mut self) -> Result<Type, LocatedError> {
        use self::Parse::*;
        match self.next()? {
            Some(Located(_, Token::Int)) => Parsed(Type::Int),
            Some(l) => Other(l),
            None => EOF(self.position()),
        }.ok_or("atomic type")
    }
}

impl Token {
    fn is_right_arrow(&self) -> bool {
        match *self {
            Token::RArrow => true,
            _ => false,
        }
    }
}

impl Error {
    fn expect(s: &str, t: Token) -> Error {
        Error::Expect(String::from(s), t)
    }

    fn is_eof(&self) -> bool {
        match *self {
            Error::EOF(_) => true,
            _ => false,
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::Io(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;
        match *self {
            EOF(ref s) => write!(f, "unexpected end of file, but want {}", s),
            Io(ref e) => e.fmt(f),
            Expect(ref s, ref t) => write!(f, "got {:#}, but expected {}", t, s),
            Trailing(ref t) => write!(f, "trailing {:#}, but expected end of file", t),
            Illegal(b) => write!(f, "illegal byte {:?}", b as char),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        use self::Error::*;
        match *self {
            EOF(..) => "unexpected end of file whereas expected an expression denoted by a string",
            Io(ref e) => e.description(),
            Expect(..) => "expected an expression denoted by a string, but got a token",
            Trailing(..) => "given a trailing token, but expected end of file",
            Illegal(..) => "given an illegal byte",
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::*;
        if f.alternate() {
            match *self {
                Number(n) => write!(f, "{}", n),
                Ident(ref s) => write!(f, "{:?}", s),
                Int => write!(f, "int"),
                Lambda => write!(f, "lambda"),
                RArrow => write!(f, "right arrow"),
                Colon => write!(f, "colon"),
                Dot => write!(f, "dot"),
                BinOp(ref k) => k.fmt(f),
            }
        } else {
            match *self {
                Number(n) => write!(f, "{}", n),
                Ident(ref s) => write!(f, "{}", s),
                Int => write!(f, "int"),
                Lambda => write!(f, "\\"),
                RArrow => write!(f, "->"),
                Colon => write!(f, ":"),
                Dot => write!(f, "."),
                BinOp(ref k) => k.fmt(f),
            }
        }
    }
}

impl fmt::Display for BinOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::BinOpKind::*;
        if f.alternate() {
            match *self {
                Plus => write!(f, "plus"),
                Minus => write!(f, "minus"),
            }
        } else {
            match *self {
                Plus => write!(f, "+"),
                Minus => write!(f, "-"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        let mut l = Lexer::new("a".as_bytes().bytes()).unwrap();
        assert_eq!(
            l.lex().ok(),
            Some(Some(Located(
                Position(1, 1),
                Token::Ident(String::from("a"))
            )))
        );
        assert!(l.lex().unwrap().is_none());

        let mut l = Lexer::new("..".as_bytes().bytes()).unwrap();
        assert_eq!(
            l.lex().ok(),
            Some(Some(Located(Position(1, 1), Token::Dot)))
        );
        assert_eq!(
            l.lex().ok(),
            Some(Some(Located(Position(1, 2), Token::Dot)))
        );
        assert!(l.lex().unwrap().is_none());
    }

    #[test]
    fn test_parse() {
        use self::Expr::*;
        use self::Term;
        use self::Term::*;

        let var = |s| Term(Var(String::from(s)));
        let int = |n| Term(Int(n));

        macro_rules! assert_parse {
            ($s:expr, $t:expr) => {
                match parse($s.as_bytes()) {
                    Ok(x) => assert_eq!(x, $t),
                    Err(e) => panic!("{}", e),
                }
            }
        }

        assert_parse!("x", var("x"));

        assert_parse!("x y", Term(Term::app(var("x"), var("y"))));

        assert_parse!(
            "x y z",
            Term(Term::app(Term(Term::app(var("x"), var("y"))), var("z")))
        );

        assert_parse!(
            "\\x:int.12 y 3",
            Term(Abs(
                String::from("x"),
                Type::Int,
                Box::new(Term(Term::app(Term(Term::app(int(12), var("y"))), int(3))),),
            ))
        );

        assert_parse!(
            "\\x:int -> int.\\ y : int . 9",
            Term(Abs(
                String::from("x"),
                Type::arr(Type::Int, Type::Int),
                Box::new(Term(Abs(String::from("y"), Type::Int, Box::new(int(9)))),),
            ))
        );

        assert_parse!("x + y", Expr::add(var("x"), var("y")));

        assert_parse!(
            "x + y - z",
            Expr::sub(Expr::add(var("x"), var("y")), var("z"))
        );
    }
}
