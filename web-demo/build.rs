use std::process::Command;

fn main() {
    Command::new("wasm-pack")
        .args(&["build", "--target=web", "--out-dir=../static/validator"])
        .current_dir("./wasm-validator")
        .spawn()
        .expect("Failed to start wasm-pack")
        .wait()
        .expect("Error awaiting wasm-pack");
}
