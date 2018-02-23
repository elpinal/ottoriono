extern crate ottoriono;

use ottoriono::parse;
use ottoriono::parse::LocatedError;

use std::error;
use std::io;
use std::io::Write;

fn main() {
    loop {
        if let Err(e) = run() {
            eprintln!("{}", e);
        }
    }
}

fn run() -> Result<(), Box<error::Error>> {
    let stdin = io::stdin();
    let mut buf = String::new();
    loop {
        print!("ottoriono: ");
        io::stdout().flush()?;

        stdin.read_line(&mut buf)?;
        println!("{}", parse::parse(buf.as_bytes())?);

        buf.truncate(0);
    }
}
