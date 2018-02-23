use expr::{Expr, Term, Type};

use std::error;
use std::fmt;
use std::io;
use std::io::{Bytes, Read};
use std::mem;

#[derive(Debug, PartialEq)]
pub struct Located<T>(Position, T);

pub type LocatedError = Located<Error>;

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
    EOF,
    Io(io::Error),
    Unexpected(u8, u8),
    Expect(String, Token),
    Trailing(Token),
}

pub fn parse<R>(r: R) -> Result<Expr, LocatedError>
where
    R: Read,
{
    let mut p = Parser::new(r)?;
    match p.parse()? {
        Some(e) => {
            if let Some(t) = p.take() {
                Err(Located(t.0, Error::Trailing(t.1)))
            } else {
                Ok(e)
            }
        }
        None => Err(p.expect("expression")),
    }
}

#[derive(Debug, PartialEq)]
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
        self.skip_whitespace()?;
        if self.eof {
            return Ok(None);
        }
        let p = self.position();
        macro_rules! ret {
            ($x:expr) => {
                return $x.map(|o| o.map(|t| Located(p, t)));
            }
        }
        match self.current {
            b if is_digit_start(b) => ret!(self.lex_number()),
            b if is_ident_start(b) => ret!(self.lex_ident()),
            b'\\' => ret!(self.proceed(Token::Lambda)),
            b'-' => ret!(self.lex_hyphen()),
            b':' => ret!(self.proceed(Token::Colon)),
            b'.' => ret!(self.proceed(Token::Dot)),
            b'+' => ret!(self.proceed(Token::Plus)),
            _ => unimplemented!(),
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
        if self.eof {
            return Ok(Some(Token::Minus));
        }
        Ok(Some(if self.current == b'>' {
            self.next_store()?;
            Token::RArrow
        } else {
            Token::Minus
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

    fn current_or_eof(&self) -> Result<&Located<Token>, LocatedError> {
        let t = self.current.as_ref();
        t.ok_or(Located(self.position(), Error::EOF))
    }

    fn parse(&mut self) -> Result<Option<Expr>, LocatedError> {
        match self.current_or_eof()?.1 {
            Token::Lambda => {
                self.lex()?;
                self.parse_abs().map(|x| Some(x))
            }
            _ => self.parse_expr(),
        }
    }

    fn parse_expr(&mut self) -> Result<Option<Expr>, LocatedError> {
        let mut e0: Expr;
        match self.parse_term()? {
            Some(e) => e0 = e,
            None => return Ok(None),
        }
        loop {
            let t0: Token;
            match self.parse_binary_operator()? {
                Some(t) => t0 = t,
                None => return Ok(Some(e0)),
            }
            match self.parse_term()? {
                Some(e1) => match t0 {
                    Token::Plus => e0 = Expr::add(e0, e1),
                    Token::Minus => e0 = Expr::sub(e0, e1),
                    _ => unreachable!(),
                },
                None => {
                    return Err(self.expect("term"));
                }
            }
        }
    }

    fn proceed<T>(&mut self, x: T) -> Result<Option<T>, LocatedError> {
        self.lex()?;
        Ok(Some(x))
    }

    fn parse_binary_operator(&mut self) -> Result<Option<Token>, LocatedError> {
        use self::Token::*;
        Ok(match self.current {
            Some(Located(_, Plus)) => self.proceed(Plus)?,
            Some(Located(_, Minus)) => self.proceed(Minus)?,
            _ => None,
        })
    }

    fn parse_term(&mut self) -> Result<Option<Expr>, LocatedError> {
        let e0: Expr;
        match self.parse_factor()? {
            Some(e) => e0 = e,
            None => return Ok(None),
        }
        let mut v = vec![];
        loop {
            match self.parse_factor()? {
                Some(e1) => v.push(e1),
                None => {
                    return Ok(Some(
                        v.into_iter().fold(e0, |e, e1| Expr::Term(Term::app(e, e1))),
                    ))
                }
            }
        }
    }

    fn parse_factor(&mut self) -> Result<Option<Expr>, LocatedError> {
        Ok(match self.take() {
            Some(Located(_, Token::Number(n))) => self.proceed(Expr::Term(Term::Int(n as isize)))?,
            Some(Located(_, Token::Ident(s))) => self.proceed(Expr::Term(Term::Var(s)))?,
            mut current => {
                mem::swap(&mut self.current, &mut current);
                None
            }
        })
    }

    fn parse_abs(&mut self) -> Result<Expr, LocatedError> {
        macro_rules! expect {
            ($t:expr, $p:pat, $body:expr) => {
                match self.next()?.ok_or(Located(self.position(), Error::EOF))? {
                    Located(_, $p) => $body,
                    t => return Err(Located(t.0, Error::expect($t, t.1))),
                }
            }
        }
        expect!(
            "ident",
            Token::Ident(s),
            expect!("colon", Token::Colon, {
                let ty = self.parse_type()?;
                expect!("dot", Token::Dot, {
                    let body = self.parse()?.ok_or(self.expect("expression"))?;
                    return Ok(Expr::Term(Term::Abs(s, ty, Box::new(body))));
                })
            })
        );
    }

    fn expect(&self, s: &str) -> LocatedError {
        Located(
            self.position(),
            match self.current {
                Some(ref t) => Error::expect(s, t.1.clone()),
                None => Error::EOF,
            },
        )
    }

    fn parse_type(&mut self) -> Result<Type, LocatedError> {
        let a = self.parse_atomic_type()?;
        {
            if let Some(ref l) = self.current {
                if l.1 != Token::RArrow {
                    return Ok(a);
                }
            }
        }
        self.lex()?;
        let ty = self.parse_type()?;
        Ok(Type::Arr(Box::new(a), Box::new(ty)))
    }

    fn parse_atomic_type(&mut self) -> Result<Type, LocatedError> {
        macro_rules! err {
            ($e:expr) => {
                Err(Located(self.position(), $e))
            }
        }
        match self.next()? {
            Some(Located(_, Token::Int)) => Ok(Type::Int),
            Some(t) => Err(Located(t.0, Error::expect("atomic type", t.1))),
            None => err!(Error::EOF),
        }
    }
}

impl Error {
    fn expect(s: &str, t: Token) -> Error {
        Error::Expect(String::from(s), t)
    }

    fn is_eof(&self) -> bool {
        match *self {
            Error::EOF => true,
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
            EOF => write!(f, "unexpected end of file"),
            Io(ref e) => e.fmt(f),
            Unexpected(got, want) => {
                write!(f, "got {:?}, but want {:?}", got as char, want as char)
            }
            Expect(ref s, ref t) => write!(f, "got {:#}, but expected {}", t, s),
            Trailing(ref t) => write!(f, "trailing {:#}, but expected end of file", t),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        use self::Error::*;
        match *self {
            EOF => "unexpected end of file",
            Io(ref e) => e.description(),
            Unexpected(..) => "given an unexpected byte whereas another byte expected",
            Expect(..) => "expected an expression denoted by a string, but got a token",
            Trailing(..) => "given a trailing token, but expected end of file",
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
                Plus => write!(f, "plus"),
                Minus => write!(f, "minus"),
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
        assert_eq!(l.lex().ok(), Some(Some(Located(Position(1, 1), Token::Ident(String::from("a"))))));
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
                let mut p = Parser::new($s.as_bytes()).unwrap();
                match p.parse() {
                    Ok(x) => assert_eq!(x, Some($t)),
                    Err(e) => panic!("{}: {}", p.position(), e),
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
