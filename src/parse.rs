use expr;

use std::io::Read;

enum Error {
}

fn parse<R>(mut r: R) -> Result<expr::Expr, Error>
where
    R: Read,
{
    let mut buf = [0; 10];
    r.read(&mut buf);
    match buf[0] {
        b'0'...b'9' => {
            return Ok(expr::Expr::Term(expr::Term::Int((buf[0] - b'0') as isize)));
        }
        _ => unimplemented!(),
    }
}
