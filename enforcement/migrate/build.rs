use enforcement::translate;

fn main() {
    translate::translate_policy_file("policy.txt", "types.rs");
}
