use expr::{Expr, Term, Type};

use std::fmt;
use std::io;
use std::io::{Bytes, Read};
use std::mem;

#[derive(Debug)]
pub enum Error {
    EOF,
    Io(io::Error),
    Unexpected(u8, u8),
    Expect(String, Token),
    Trailing(Token),
}

pub fn parse<R>(r: R) -> Result<Expr, Error>
where
    R: Read,
{
    let mut p = Parser::new(r)?;
    match p.parse()? {
        Some(e) => {
            if let Some(t) = p.take() {
                Err(Error::Trailing(t))
            } else {
                Ok(e)
            }
        }
        None => Err(p.expect("expression")),
    }
}

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
    current: Option<Token>,
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
    fn new(b: Bytes<R>) -> Result<Lexer<R>, Error> {
        let mut l = Lexer {
            b,
            current: 0,
            eof: false,
            line: 0,
            column: 0,
        };
        l.next_store()?;
        Ok(l)
    }

    fn from_read(r: R) -> Result<Lexer<R>, Error> {
        Lexer::new(r.bytes())
    }

    /// Return the position. Its line and column are start from 1.
    fn position(&self) -> Position {
        Position(self.line + 1, self.column + 1)
    }

    fn next_store(&mut self) -> Result<(), Error> {
        if let Some(r) = self.next() {
            self.current = r?;
        } else {
            self.eof = true;
        }
        Ok(())
    }

    fn next(&mut self) -> Option<Result<u8, Error>> {
        let ret = self.b.next().map(|r| r.map_err(|e| Error::Io(e)));
        if let Some(Ok(b)) = ret {
            if b == b'\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
        }
        ret
    }

    fn lex(&mut self) -> Result<Option<Token>, Error> {
        self.skip_whitespace()?;
        if self.eof {
            return Ok(None);
        }
        match self.current {
            b if is_digit_start(b) => return self.lex_number(),
            b if is_ident_start(b) => return self.lex_ident(),
            b'\\' => return self.proceed(Token::Lambda),
            b'-' => return self.lex_hyphen(),
            b':' => return self.proceed(Token::Colon),
            b'.' => return self.proceed(Token::Dot),
            b'+' => return self.proceed(Token::Plus),
            _ => unimplemented!(),
        }
    }

    fn lex_number(&mut self) -> Result<Option<Token>, Error> {
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

    fn lex_ident(&mut self) -> Result<Option<Token>, Error> {
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

    fn proceed(&mut self, t: Token) -> Result<Option<Token>, Error> {
        self.next_store()?;
        Ok(Some(t))
    }

    fn lex_hyphen(&mut self) -> Result<Option<Token>, Error> {
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

    fn skip_whitespace(&mut self) -> Result<(), Error> {
        while !self.eof && is_whitespace(self.current) {
            self.next_store()?;
        }
        Ok(())
    }
}

impl<R: Read> Parser<R> {
    fn new(r: R) -> Result<Parser<R>, Error> {
        let l = Lexer::from_read(r)?;
        Parser::from_lexer(l)
    }

    fn from_lexer(mut lexer: Lexer<R>) -> Result<Parser<R>, Error> {
        let t = lexer.lex()?;
        Ok(Parser { lexer, current: t })
    }

    fn position(&self) -> Position {
        self.lexer.position()
    }

    fn lex(&mut self) -> Result<(), Error> {
        self.current = self.lexer.lex()?;
        Ok(())
    }

    fn next(&mut self) -> Result<Option<Token>, Error> {
        self.lexer.lex().map(|t| mem::replace(&mut self.current, t))
    }

    fn take(&mut self) -> Option<Token> {
        mem::replace(&mut self.current, None)
    }

    fn current_or_eof(&self) -> Result<&Token, Error> {
        let t: Option<&Token> = self.current.as_ref();
        t.ok_or(Error::EOF)
    }

    fn parse(&mut self) -> Result<Option<Expr>, Error> {
        match self.current_or_eof()? {
            &Token::Lambda => {
                self.lex()?;
                self.parse_abs().map(|x| Some(x))
            }
            _ => self.parse_expr(),
        }
    }

    fn parse_expr(&mut self) -> Result<Option<Expr>, Error> {
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

    fn proceed<T>(&mut self, x: T) -> Result<Option<T>, Error> {
        self.lex()?;
        Ok(Some(x))
    }

    fn parse_binary_operator(&mut self) -> Result<Option<Token>, Error> {
        use self::Token::*;
        Ok(match self.current {
            Some(Plus) => self.proceed(Plus)?,
            Some(Minus) => self.proceed(Minus)?,
            _ => None,
        })
    }

    fn parse_term(&mut self) -> Result<Option<Expr>, Error> {
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

    fn parse_factor(&mut self) -> Result<Option<Expr>, Error> {
        Ok(match self.take() {
            Some(Token::Number(n)) => self.proceed(Expr::Term(Term::Int(n as isize)))?,
            Some(Token::Ident(s)) => self.proceed(Expr::Term(Term::Var(s)))?,
            mut current => {
                mem::swap(&mut self.current, &mut current);
                None
            }
        })
    }

    fn parse_abs(&mut self) -> Result<Expr, Error> {
        macro_rules! expect {
            ($t:expr, $p:pat, $body:expr) => {
                match self.next()?.ok_or(Error::EOF)? {
                    $p => $body,
                    t => return Err(Error::expect($t, t)),
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

    fn expect(&self, s: &str) -> Error {
        match self.current {
            Some(ref t) => Error::expect(s, t.clone()),
            None => Error::EOF,
        }
    }

    fn parse_type(&mut self) -> Result<Type, Error> {
        let a = self.parse_atomic_type()?;
        {
            if self.current != Some(Token::RArrow) {
                return Ok(a);
            }
        }
        self.lex()?;
        let ty = self.parse_type()?;
        Ok(Type::Arr(Box::new(a), Box::new(ty)))
    }

    fn parse_atomic_type(&mut self) -> Result<Type, Error> {
        match self.next()? {
            Some(Token::Int) => Ok(Type::Int),
            Some(t) => Err(Error::expect("atomic type", t)),
            None => Err(Error::EOF),
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
        assert_eq!(l.lex().ok(), Some(Some(Token::Ident(String::from("a")))));
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
