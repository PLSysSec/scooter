use std::process::{Command, Stdio};

fn main() {
    println!("cargo:rerun-if-changed=static/validator");
    println!("cargo:rerun-if-changed=web-demo");
    Command::new("wasm-pack")
        .args(&["build", "--target=web", "--out-dir=../static/validator"])
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/wasm-validator"))
        // eat stdout just in case something leaks out a cargo directive
        .stdout(Stdio::piped())
        .spawn()
        .expect("Error spawning wasm-pack")
        .wait()
        .expect("Error waiting for wasm-pack");
}
