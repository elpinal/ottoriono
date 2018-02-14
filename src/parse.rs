use expr::{Expr, Term, Type};

use std::io;
use std::io::{Bytes, Read};
use std::mem;

#[derive(Debug)]
pub enum Error {
    EOF,
    Io(io::Error),
    Unexpected(u8, u8),
    Expect(String, Token),
}

pub fn parse<R>(r: R) -> Result<Expr, Error>
where
    R: Read,
{
    let mut buf = Parser::new(Lexer::new(r.bytes())?)?;
    buf.parse()
}

struct Lexer<R> {
    b: Bytes<R>,
    current: u8,
    eof: bool,
}

struct Parser<R> {
    lexer: Lexer<R>,
    current: Option<Token>,
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

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Number(usize),
    Ident(String),
    Int,
    Lambda,
    RArrow,
    Colon,
    Dot,
}

impl<R: Read> Lexer<R> {
    fn new(b: Bytes<R>) -> Result<Lexer<R>, Error> {
        let mut l = Lexer {
            b,
            current: 0,
            eof: false,
        };
        l.next_store()?;
        Ok(l)
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
        self.b.next().map(|r| r.map_err(|e| Error::Io(e)))
    }

    fn lex(&mut self) -> Result<Token, Error> {
        self.skip_whitespace()?;
        if self.eof {
            return Err(Error::EOF);
        }
        match self.current {
            b if is_digit_start(b) => return self.lex_number(),
            b if is_ident_start(b) => return self.lex_ident(),
            b'\\' => return self.proceed(Token::Lambda),
            b'-' => return self.lex_right_arrow(),
            b':' => return self.proceed(Token::Colon),
            b'.' => return self.proceed(Token::Dot),
            _ => unimplemented!(),
        }
    }

    fn lex_number(&mut self) -> Result<Token, Error> {
        let f = |buf: &Lexer<_>| (buf.current - b'0') as usize;
        let mut n = f(self);
        loop {
            self.next_store()?;
            if self.eof || !is_digit(self.current) {
                return Ok(Token::Number(n));
            }
            n = n * 10 + f(self)
        }
    }

    fn lex_ident(&mut self) -> Result<Token, Error> {
        let mut vec = vec![];
        vec.push(self.current);
        loop {
            self.next_store()?;
            if self.eof || !is_ident(self.current) {
                let s = unsafe { String::from_utf8_unchecked(vec) };
                return Ok(if s == "int" {
                    Token::Int
                } else {
                    Token::Ident(s)
                });
            }
            vec.push(self.current);
        }
    }

    fn proceed(&mut self, t: Token) -> Result<Token, Error> {
        self.next_store()?;
        Ok(t)
    }

    fn lex_right_arrow(&mut self) -> Result<Token, Error> {
        self.next_store()?;
        if self.eof {
            return Err(Error::EOF);
        }
        match self.current {
            b'>' => {
                self.next_store()?;
                Ok(Token::RArrow)
            }
            b => Err(Error::Unexpected(b, b'>')),
        }
    }

    fn skip_whitespace(&mut self) -> Result<(), Error> {
        while !self.eof && is_whitespace(self.current) {
            self.next_store()?;
        }
        Ok(())
    }
}

impl<R: Read> Parser<R> {
    fn new(mut lexer: Lexer<R>) -> Result<Parser<R>, Error> {
        let t = lexer.lex()?;
        Ok(Parser {
            lexer,
            current: Some(t),
        })
    }

    fn lex(&mut self) -> Result<(), Error> {
        self.current = Some(self.lexer.lex()?);
        Ok(())
    }

    fn next(&mut self) -> Result<Option<Token>, Error> {
        match self.lexer.lex() {
            Err(ref e) if e.is_eof() => Ok(self.take()),
            Err(e) => Err(e),
            Ok(t) => Ok(mem::replace(&mut self.current, Some(t))),
        }
    }

    fn take(&mut self) -> Option<Token> {
        mem::replace(&mut self.current, None)
    }

    fn current_or_eof(&self) -> Result<&Token, Error> {
        let t: Option<&Token> = self.current.as_ref();
        t.ok_or(Error::EOF)
    }

    fn parse(&mut self) -> Result<Expr, Error> {
        match self.current_or_eof()? {
            &Token::Lambda => {
                self.lex()?;
                self.parse_abs()
            }
            _ => self.parse_expr(),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Error> {
        self.parse_term()
    }

    fn parse_term(&mut self) -> Result<Expr, Error> {
        let e0 = self.parse_factor()?.ok_or_else(
            || match self.current_or_eof() {
                Ok(t) => Error::expect("factor", t.clone()),
                Err(e) => e,
            },
        )?;
        let mut v = vec![];
        loop {
            match self.parse_factor()? {
                Some(e1) => v.push(e1),
                None => return Ok(v.into_iter().fold(e0, |e, e1| Expr::Term(Term::app(e, e1)))),
            }
        }
    }

    fn parse_factor(&mut self) -> Result<Option<Expr>, Error> {
        macro_rules! proceed {
            ($e:expr) => {
                {
                    self.next()?;
                    Some(Expr::Term($e))
                }
            }
        }
        Ok(match self.take() {
            Some(Token::Number(n)) => proceed!(Term::Int(n as isize)),
            Some(Token::Ident(s)) => proceed!(Term::Var(s)),
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
                    let body = self.parse()?;
                    return Ok(Expr::Term(Term::Abs(s, ty, Box::new(body))));
                })
            })
        );
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        let mut l = Lexer::new("a".as_bytes().bytes()).unwrap();
        assert_eq!(l.lex().ok(), Some(Token::Ident(String::from("a"))));
        assert!(l.lex().unwrap_err().is_eof());
    }

    #[test]
    fn test_parse() {
        use self::Expr::*;
        use self::Term;
        use self::Term::*;

        let var = |s| Term(Var(String::from(s)));
        let int = |n| Term(Int(n));

        assert_eq!(parse("x".as_bytes()).ok(), Some(var("x")));

        assert_eq!(
            parse("x y".as_bytes()).ok(),
            Some(Term(Term::app(var("x"), var("y"))))
        );

        assert_eq!(
            parse("x y z".as_bytes()).ok(),
            Some(Term(
                Term::app(Term(Term::app(var("x"), var("y"))), var("z")),
            ))
        );

        assert_eq!(
            parse("\\x:int.12 y 3".as_bytes()).ok(),
            Some(Term(Abs(
                String::from("x"),
                Type::Int,
                Box::new(
                    Term(Term::app(Term(Term::app(int(12), var("y"))), int(3))),
                ),
            )))
        );

        assert_eq!(
            parse("\\x:int -> int.\\ y : int . 9".as_bytes()).ok(),
            Some(Term(Abs(
                String::from("x"),
                Type::arr(Type::Int, Type::Int),
                Box::new(
                    Term(Abs(String::from("y"), Type::Int, Box::new(int(9)))),
                ),
            )))
        );
    }
}
