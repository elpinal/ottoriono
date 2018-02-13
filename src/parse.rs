use expr::{Expr, Term};

use std::io;
use std::io::{Bytes, Read};

pub enum Error {
    EOF,
    Io(io::Error),
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
        loop {
            match self.current {
                b if is_whitespace(b) => (),
                b if is_digit_start(b) => return self.parse_int(),
                b if is_ident_start(b) => return self.parse_var(),
                _ => unimplemented!(),
            }
        }
    }

    fn parse_int(&mut self) -> Result<Expr, Error> {
        let f = |buf: &Wrapper<_>| (buf.current - b'0') as isize;
        let mut n = f(self);
        loop {
            self.next_store()?;
            match self.current {
                b if is_digit(b) => n = n * 10 + f(self),
                _ => return Ok(Expr::Term(Term::Int(n))),
            }
        }
    }

    fn parse_var(&mut self) -> Result<Expr, Error> {
        let s = self.parse_ident()?;
        Ok(Expr::Term(Term::Var(s)))
    }

    fn parse_ident(&mut self) -> Result<String, Error> {
        let mut vec = vec![];
        vec.push(self.current);
        loop {
            self.next_store()?;
            match self.current {
                b if is_ident(b) => vec.push(b),
                _ => {
                    let s = unsafe { String::from_utf8_unchecked(vec) };
                    return Ok(s);
                }
            }
        }
    }

    fn skip_whitespace(&mut self) -> Result<(), Error> {
        while is_whitespace(self.current) {
            self.next_store()?;
        }
        Ok(())
    }
}
