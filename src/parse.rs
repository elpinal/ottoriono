use expr;

use std::io::Read;

enum Error {
    EOF,
}

fn parse<R>(mut r: R) -> Result<expr::Expr, Error>
where
    R: Read,
{
    let mut buf = r.bytes();
    let b = buf.next();
    match b {
        b'0'...b'9' => {
            return Ok(expr::Expr::Term(expr::Term::Int((b - b'0') as isize)));
        }
        _ => unimplemented!(),
    }
}
