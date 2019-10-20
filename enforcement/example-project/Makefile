
all: test

test: src/types.rs
	cargo test

src/types.rs: policy.txt
	cd ../ && cargo run --bin translate example-project/policy.txt > example-project/src/types.rs
