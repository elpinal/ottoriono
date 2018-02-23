extern crate ottoriono;

use ottoriono::parse;
use ottoriono::parse::Error;

use std::io;
use std::process::exit;

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        exit(1);
    }
}

fn run() -> Result<(), Error> {
    let stdin = io::stdin();
    let mut buf = String::new();
    loop {
        stdin.read_line(&mut buf)?;
        println!("{}", parse::parse(buf.as_bytes())?);
        buf.truncate(0);
    }
}
