extern crate ottoriono;

use ottoriono::parse;

use std::io;

fn main() {
    let stdin = io::stdin();
    let handle = stdin.lock();
    match parse::parse(handle) {
        Ok(e) => println!("{}", e),
        Err(e) => eprintln!("{}", e),
    }
}
