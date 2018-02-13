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
    match buf.current {
        b'0'...b'9' => {
            return Ok(Expr::Term(Term::Int((buf.current - b'0') as isize)));
        }
        _ => unimplemented!(),
    }
}

struct Wrapper<R> {
    b: Bytes<R>,
    current: u8,
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
}
