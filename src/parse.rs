use expr;

use std::io;
use std::io::{Bytes, Read};

enum Error {
    EOF,
    Io(io::Error),
}

fn parse<R>(r: R) -> Result<expr::Expr, Error>
where
    R: Read,
{
    let mut buf = Wrapper { b: r.bytes() };
    let b = buf.next()?;
    match b {
        b'0'...b'9' => {
            return Ok(expr::Expr::Term(expr::Term::Int((b - b'0') as isize)));
        }
        _ => unimplemented!(),
    }
}

struct Wrapper<R> {
    b: Bytes<R>,
}

impl<R: Read> Wrapper<R> {
    fn next(&mut self) -> Result<u8, Error> {
        match self.b.next() {
            Some(r) => r.map_err(|e| Error::Io(e)),
            None => Err(Error::EOF),
        }
    }
}
