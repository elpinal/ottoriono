use expr::{Expr, Term};

use std::io;
use std::io::{Bytes, Read};

enum Error {
    EOF,
    Io(io::Error),
}

fn parse<R>(r: R) -> Result<Expr, Error>
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

impl<R: Read> Wrapper<R> {
    fn new(b: Bytes<R>) -> Wrapper<R> {
        Wrapper { b, current: 0 }
    }

    fn next_store(&mut self) -> Result<(), Error> {
        let b = self.next()?;
        self.current = b;
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
                b if is_digit_start(b) => return self.parse_int(),
                b if is_whitespace(b) => (),
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
}
