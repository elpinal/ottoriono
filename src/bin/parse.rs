extern crate ottoriono;

use ottoriono::parse;
use ottoriono::parse::Error;

use std::io;
use std::io::Write;

fn main() {
    loop {
        if let Err(e) = run() {
            eprintln!("{}", e);
        }
    }
}

fn run() -> Result<(), Error> {
    let stdin = io::stdin();
    let mut buf = String::new();
    loop {
        print!("ottoriono: ");
        io::stdout().flush().unwrap();

        stdin.read_line(&mut buf)?;
        println!("{}", parse::parse(buf.as_bytes())?);

        buf.truncate(0);
    }
}
