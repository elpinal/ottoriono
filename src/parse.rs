use expr;

use std::io::Read;

enum Error {
}

fn parse<R>(r: R) -> Result<expr::Expr, Error>
where
    R: Read,
{
    unimplemented!();
}
