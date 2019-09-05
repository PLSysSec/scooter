use crate::Schema;
use std::io::Write;
use std::process::{Command, Stdio};

const logic: &str = include_str!("../tra.smt2");

/// Determines if a is a subset of b
pub fn is_subset(s: &Schema, a: impl ToString, b: impl ToString) -> bool {
    let mut z3_cmd = Command::new("z3")
        .args(&["-smt2", "-in"])
        .stdout(Stdio::piped())
        .stdin(Stdio::piped())
        .spawn()
        .expect("Unable to launch z3");
    {
        let mut input = z3_cmd.stdin.as_mut().unwrap();
        write_out(input, s, a, b);
    }
    let out = z3_cmd.wait_with_output().unwrap();

    let out_str = std::str::from_utf8(&out.stdout).unwrap();
    println!("{}", &out_str);
    return out_str == "unsat\n";
}

fn write_out(mut out: &mut dyn Write, s: &Schema, a: impl ToString, b: impl ToString) {
    let mut builder = s.builder();

    let assert_a = builder.to_smt(a.to_string());
    let assert_b = builder.to_smt(b.to_string());
    let preamble = builder.preamble();

    out.write_all("(push)\n".as_bytes());
    out.write_all(logic.as_bytes());
    out.write_all(preamble.as_bytes());
    write!(
        &mut out,
        "(assert (not (sub-set {} {})))\n",
        assert_a, assert_b
    );
    write!(&mut out, "{}", "(check-sat)");
}

#[test]
fn test() {
    let schema: Schema =
        toml::from_str(r#"user = ["uid", "name", "age"]"#).expect("this should parse...");

    let res = is_subset(
        &schema,
        "SELECT * FROM user WHERE name = 4",
        "SELECT * FROM user",
    );

    assert!(res)
}
