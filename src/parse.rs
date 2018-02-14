use expr::{Expr, Term, Type};

use std::io;
use std::io::{Bytes, Read};
use std::mem;

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
}

struct Parser<R> {
    lexer: Lexer<R>,
    current: Token,
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

#[derive(Clone, PartialEq)]
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
        let mut l = Lexer { b, current: 0 };
        l.next_store()?;
        Ok(l)
    }

    fn next_store(&mut self) -> Result<(), Error> {
        self.current = self.next()?;
        Ok(())
    }

    fn next(&mut self) -> Result<u8, Error> {
        match self.b.next() {
            Some(r) => r.map_err(|e| Error::Io(e)),
            None => Err(Error::EOF),
        }
    }

    fn lex(&mut self) -> Result<Token, Error> {
        self.skip_whitespace()?;
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
            match self.current {
                b if is_digit(b) => n = n * 10 + f(self),
                _ => return Ok(Token::Number(n)),
            }
        }
    }

    fn lex_ident(&mut self) -> Result<Token, Error> {
        let mut vec = vec![];
        vec.push(self.current);
        loop {
            self.next_store()?;
            match self.current {
                b if is_ident(b) => vec.push(b),
                _ => {
                    let s = unsafe { String::from_utf8_unchecked(vec) };
                    return Ok(if s == "int" {
                        Token::Int
                    } else {
                        Token::Ident(s)
                    });
                }
            }
        }
    }

    fn proceed(&mut self, t: Token) -> Result<Token, Error> {
        self.next_store()?;
        Ok(t)
    }

    fn lex_right_arrow(&mut self) -> Result<Token, Error> {
        self.next_store()?;
        match self.current {
            b'>' => {
                self.next_store()?;
                Ok(Token::RArrow)
            }
            b => Err(Error::Unexpected(b, b'>')),
        }
    }

    fn skip_whitespace(&mut self) -> Result<(), Error> {
        while is_whitespace(self.current) {
            self.next_store()?;
        }
        Ok(())
    }
}

impl<R: Read> Parser<R> {
    fn new(mut lexer: Lexer<R>) -> Result<Parser<R>, Error> {
        let t = lexer.lex()?;
        Ok(Parser { lexer, current: t })
    }

    fn lex(&mut self) -> Result<(), Error> {
        self.current = self.lexer.lex()?;
        Ok(())
    }

    fn next(&mut self) -> Result<Token, Error> {
        let next = self.lexer.lex()?;
        Ok(mem::replace(&mut self.current, next))
    }

    fn parse(&mut self) -> Result<Expr, Error> {
        match self.current {
            Token::Lambda => self.parse_abs(),
            _ => self.parse_expr(),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Error> {
        self.parse_term()
    }

    fn parse_term(&mut self) -> Result<Expr, Error> {
        let e0 = self.parse_factor()?.ok_or_else(|| {
            Error::expect("factor", self.current.clone())
        })?;
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
                    let mut next = self.lexer.lex()?;
                    mem::swap(&mut self.current, &mut next);
                    mem::forget(next);
                    Some(Expr::Term($e))
                }
            }
        }
        let mut current = mem::replace(&mut self.current, unsafe { mem::uninitialized() });
        Ok(match current {
            Token::Number(n) => proceed!(Term::Int(n as isize)),
            Token::Ident(s) => proceed!(Term::Var(s)),
            _ => {
                mem::swap(&mut self.current, &mut current);
                mem::forget(current);
                None
            }
        })
    }

    fn parse_abs(&mut self) -> Result<Expr, Error> {
        macro_rules! expect {
            ($t:expr, $p:pat, $body:expr) => {
                match self.next()? {
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
        if self.current == Token::RArrow {
            self.lex()?;
            let ty = self.parse_type()?;
            Ok(Type::Arr(Box::new(a), Box::new(ty)))
        } else {
            Err(Error::expect("right arrow", self.current.clone()))
        }
    }

    fn parse_atomic_type(&mut self) -> Result<Type, Error> {
        match self.next()? {
            Token::Int => Ok(Type::Int),
            t => Err(Error::expect("atomic type", t)),
        }
    }
}

impl Error {
    fn expect(s: &str, t: Token) -> Error {
        Error::Expect(String::from(s), t)
    }
}
