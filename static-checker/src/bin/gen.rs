use policy_lang::*;
use static_checker::smt::*;
use std::io::{self, Read};

fn get_contents(fname: &str) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}

fn main() {
    let mut args = std::env::args();
    args.next().unwrap();
    let before = args.next().unwrap();
    let after = args.next().unwrap();

    let gp_before = parse_policy(&get_contents(&before).unwrap()).unwrap();
    let gp_after = parse_policy(&get_contents(&after).unwrap()).unwrap();

    let out = gen_full(gp_before, gp_after);

    println!("{}", out);
}
