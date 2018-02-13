use expr::{Expr, Term};

use std::io;
use std::io::{Bytes, Read};

pub enum Error {
    EOF,
    Io(io::Error),
    Unexpected(u8, u8),
}

pub fn parse<R>(r: R) -> Result<Expr, Error>
where
    R: Read,
{
    let mut buf = Wrapper::new(r.bytes());
    buf.next_store()?;
    buf.parse()
}

struct Wrapper<R> {
    b: Bytes<R>,
    current: u8,
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

enum Token {
    Number(usize),
    Ident(String),
    Int,
    Lambda,
    RArrow,
    Colon,
}

impl<R: Read> Wrapper<R> {
    fn new(b: Bytes<R>) -> Wrapper<R> {
        Wrapper { b, current: 0 }
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

    fn parse(&mut self) -> Result<Expr, Error> {
        match self.lex()? {
            Token::Number(n) => Ok(Expr::Term(Term::Int(n as isize))),
            Token::Ident(s) => Ok(Expr::Term(Term::Var(s))),
            _ => unimplemented!(),
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
            _ => unimplemented!(),
        }
    }

    fn lex_number(&mut self) -> Result<Token, Error> {
        let f = |buf: &Wrapper<_>| (buf.current - b'0') as usize;
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
